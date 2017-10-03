open Core.Std

open Expression
open Type
open Task
open Library
open Enumerate
open Utils
open Compress
open Frontier
open Bottom_up


let rec expectation_maximization_compress
    lambda smoothing application_smoothing g0 dagger type_array requests candidates tasks
    program_scores (* for each task, a list of triples of (id,ll,lp) *)
    (* unormalized posterior is ll+lp *) =
  let task_posteriors = List.map program_scores ~f:(fun ss ->
      let z = List.fold_left ss ~init:Float.neg_infinity ~f:(fun a (_,ll,lp) -> lse a (ll+.lp)) in
      List.map ss ~f:(fun (i,ll,lp) -> (i,ll+.lp-.z))) in
  let candidate_rewards =
    let r = Int.Table.create () in
    List.iter candidates (fun c -> ignore(Hashtbl.add r c Float.neg_infinity));
    r
  in
  let rec reward_expression weight i =
    match extract_node dagger i with
    | ExpressionBranch(l,r) ->
      reward_expression weight l;
      reward_expression weight r;
      (try
         let old = Hashtbl.find_exn candidate_rewards i in
         Hashtbl.replace candidate_rewards ~key:i ~data:(lse old weight)
       with Not_found -> ())
    | _ -> ()
  in
  List.iter task_posteriors ~f:(fun posterior ->
      List.iter posterior ~f:(fun (i,w) -> reward_expression w i));
  (* find those productions that have enough weight to make it into the library *)
  let productions =
    (Hashtbl.to_alist candidate_rewards |>
     List.filter ~f:(fun (_,r) -> exp r > lambda) |>
     List.map ~f:(fun (i,_) -> extract_expression dagger i)) @
    (snd g0 |> List.map ~f:fst |> List.filter ~f:is_terminal) in
  let new_grammar = make_flat_library productions in
  (* assembled corpus *)
  let corpus = merge_a_list ~f:lse @@
    List.map2_exn ~f:(fun task ->
        List.map ~f:(fun (i,l) -> ((i,task.task_type),l)))
      tasks task_posteriors in
  (* fit the continuous parameters of the new grammar *)
  let likelihoods = program_likelihoods new_grammar dagger type_array requests in
  let final_grammar =
    fit_grammar smoothing ~application_smoothing new_grammar dagger type_array likelihoods corpus in
  let program_scores = List.map2_exn tasks program_scores ~f:(fun t ->
      List.map ~f:(fun (i,ll,_) -> (i,ll,Hashtbl.find_exn likelihoods (i,t.task_type)))) in
  (* check to see if we've hit a fixed point *)
  if set_equal compare_expression productions (snd g0 |> List.map ~f:fst)
  then (final_grammar,
        let ll = List.fold_left ~init:0.0 program_scores ~f:(fun a ss ->
          if List.length ss > 0
          then List.fold_left ~init:Float.neg_infinity ss ~f:(fun a (_,ll,lp) ->
            lse a (ll+.lp))
          else a) in
        let m = Float.of_int (List.length productions) in
        let n = List.fold_left ~init:0.0 program_scores ~f:(fun n f ->
            if List.length f > 0 then n +. 1.0 else n) in
        m *. (-. lambda -. 0.5 *. log n) +. ll)
  else expectation_maximization_compress lambda smoothing application_smoothing
      final_grammar dagger type_array requests candidates tasks program_scores


let expectation_maximization_iteration ?compression_tries:(compression_tries = 1)
    prefix lambda smoothing ?application_smoothing:(application_smoothing = smoothing)
    ?da:(da = 0.1) (* dirichlet for random frontiers *)
    frontier_size tasks grammar =
  let (frontiers,dagger) = enumerate_frontiers_for_tasks grammar frontier_size tasks in
  print_string "Scoring programs... \n";
  print_newline ();
  let program_scores = score_programs dagger frontiers tasks in
  (*let () = List.hd_exn (List.map ~f:(fun i ->  Printf.printf "%i: %f    " (fst(i)) (snd(i))) (List.hd_exn program_scores)) in
  let () = print_newline () in*)
  (* display the hit rate *)
  let number_hit = List.length (List.filter ~f:(fun scores ->
      List.exists scores (fun (_,s) -> s > log (0.999))
    ) program_scores) in
  let number_of_partial = List.length (List.filter ~f:(fun scores ->
      List.length scores > 0
    ) program_scores) in
  Printf.printf "Hit %i / %i \n" number_hit (List.length tasks);
  Printf.printf "Partial credit %i / %i \n" (number_of_partial-number_hit) (List.length tasks);
  (* compute likelihoods under grammar and then normalize the frontiers *)
  let type_array = infer_graph_types dagger in
  let requests = frontier_requests frontiers in
  let candidates = candidate_ground_fragments dagger @@ List.map program_scores (List.map ~f:fst) in
  let g0 = make_flat_library @@ List.filter ~f:is_terminal @@ List.map ~f:fst @@ snd grammar in
  (* makes the nth (random) frontiers *)
  Printf.printf "Calculating random frontier";
  print_newline ();
  let random_frontier n s =
    Random.init s;
    match n with
    | 1 ->  (* nonrandom case *)
      let likelihoods = program_likelihoods grammar dagger type_array requests in
      (grammar, List.map2_exn tasks program_scores ~f:(fun t f ->
           List.map f ~f:(fun (i,ll) -> (i,ll,Hashtbl.find_exn likelihoods (i,t.task_type)))))
    | 2 -> (* uniform case *)
      (grammar, List.map program_scores ~f:(fun f ->
           List.map f ~f:(fun (i,ll) -> (i,ll,0.0))))
    | 3 ->  (* weighted by g0 *)
      let g0_likelihoods = program_likelihoods g0 dagger type_array requests in
      (g0, List.map2_exn tasks program_scores ~f:(fun t f ->
           List.map f ~f:(fun (i,ll) -> (i,ll,Hashtbl.find_exn g0_likelihoods (i,t.task_type)))))
    | _ -> (* random case *)
      (g0, List.map program_scores ~f:(fun f ->
           let lps = List.length f |> sample_uniform_dirichlet da |>
                     List.map ~f:log in
           List.map2_exn lps f ~f:(fun lp (i,ll) -> (i,ll,lp)))) in
  let ct_sd = List.zip_exn (1--compression_tries) @@ make_random_seeds compression_tries in
  Printf.printf "Candidate Grammar";
  print_newline ();
  let start_time = time () in
  let candidate_grammars = parallel_map ct_sd ~f:(fun (ct,sd) ->
    let (g0,fs) = random_frontier ct sd in
    expectation_maximization_compress lambda smoothing application_smoothing g0 dagger
      type_array requests candidates tasks fs) in
  let end_time = time () in
  Printf.printf "Candidate grammars in %f" (end_time-.start_time);
  print_newline ();
  let (final_grammar,_) = maximum_by ~cmp:(fun (_,a) (_,b) -> compare a b) candidate_grammars in
  (* save the grammar *)
  Out_channel.write_all (prefix^"_grammar") ~data:(string_of_library final_grammar);
  print_newline ();
  (* save the best programs *)
  Printf.printf "Calculating task solutions";
  print_newline ();

  let start_time = time () in
  let task_solutions = List.zip_exn tasks program_scores |> List.map ~f:(fun (t,solutions) ->
      (t, List.map solutions (fun (i,s) ->
           let e = extract_expression dagger i in
           let error_message = "em_best: "^(string_of_expression e) in
           (*let () = print_string error_message in
           let () = print_float s in
           let () = print_newline () in*)
           (i,s+. (safe_get_some error_message @@ likelihood_option final_grammar t.task_type e))))) in
  (*let a = List.map ~f:(fun i -> Printf.printf "%i: %f   - " (fst(i)) (snd(i)) ) (snd (List.hd_exn task_solutions)) in*)
  let end_time = time () in
  Printf.printf "Task solutions in %f" (end_time-.start_time);
  print_newline ();
  save_best_programs (prefix^"_programs") dagger task_solutions;
  Printf.printf "Calculating surrogate";
  print_newline ();
  ignore(bic_posterior_surrogate lambda dagger final_grammar task_solutions);
  final_grammar



let backward_iteration
    prefix lambda smoothing frontier_size keep_size
    tasks grammar = grammar
(* backwards search did not work well anyways *)
(*
  let (dagger,frontiers) = make_frontiers frontier_size keep_size grammar tasks in
  let type_array = infer_graph_types dagger in
  print_endline "Done inferring graph types.";
  let requests = frontier_requests frontiers in
  print_endline "Done getting requests.";
  let task_solutions = List.zip_exn tasks @@
    List.map frontiers (List.map ~f:(fun (i,l,_) -> (i,l)))
  in
  (* the following lines are for running EM *)
  let solutions = List.map task_solutions ((List.map ~f:fst) % snd) in
  let candidates = candidate_fragments dagger solutions in
  let g = expectation_maximization_compress
      lambda smoothing smoothing grammar dagger type_array requests candidates tasks @@
    List.map task_solutions (fun (_,) -> ) in
  (*   let g = compress lambda smoothing dagger type_array requests task_solutions in *)
  (* save the grammar *)
  Out_channel.write_all (prefix^"_grammar") ~data:(string_of_library g);
  (* save the best programs *)
  let task_solutions = List.zip_exn tasks frontiers in
  save_best_programs (prefix^"_programs") dagger task_solutions;
  g
*)
