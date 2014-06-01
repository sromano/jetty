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
    lambda smoothing g0 dagger type_array requests candidates tasks program_scores = 
  let likelihoods = program_likelihoods g0 dagger type_array requests in
  let task_posteriors = 
    List.map2_exn ~f:(fun task scores ->
        let scores = List.map scores (fun (i,s) -> 
            (i,s+. Hashtbl.find_exn likelihoods (i,task.task_type)))  in
        let z = lse_list (List.map ~f:snd scores) in
        List.map scores (fun (i,s) -> (i,s-.z)) 
      ) tasks program_scores in
  (* compute rewards for each expression *)
  let make_candidate_rewards () = 
    let r = Int.Table.create () in
    List.iter candidates (fun c -> ignore(Hashtbl.add r c Float.neg_infinity));
    r
  in
  let candidate_likelihood = memorize (fun (c,r) -> 
    match likelihood_option g0 r @@ extract_expression dagger c with
    | None -> Float.neg_infinity
    | Some(l) -> l) in
  let rec reward_expression candidate_rewards weight request i =
    match extract_node dagger i with
    | ExpressionBranch(l,r) -> 
      let left_request = function_request request in
      let right_request = argument_request request type_array.(l) in
      reward_expression candidate_rewards weight left_request l; 
      reward_expression candidate_rewards weight right_request r;
      (try
         let old = Hashtbl.find_exn candidate_rewards i in
         Hashtbl.replace candidate_rewards ~key:i ~data:(lse old weight)
       with Not_found -> (* Not a candidate - might still unify with some of them *)
         (if has_wildcards dagger i then
            let hits = List.filter candidates (can_match_wildcards dagger i) in
            if not (List.is_empty hits) then (
              let likelihoods = List.map hits (fun hit -> candidate_likelihood (hit,request)) in
              let z = lse_list likelihoods in
              if z > Float.neg_infinity then
                List.iter2_exn ~f:(fun h l -> Hashtbl.replace candidate_rewards ~key:h 
                                      ~data:(lse (weight+.l-.z) @@ Hashtbl.find_exn candidate_rewards h))
                  hits likelihoods)))
    | _ -> ()
  in 
  let rewards = parallel_map (List.zip_exn tasks task_posteriors) ~f:(fun (t,posterior) -> 
      let r = make_candidate_rewards () in
      List.iter posterior (fun (i,w) -> reward_expression r w t.task_type i);
      r) in
  let candidate_rewards = make_candidate_rewards () in
  List.iter rewards ~f:(Hashtbl.iter ~f:(fun ~key:i ~data:r -> 
    Hashtbl.replace candidate_rewards ~key:i ~data:(lse r @@ Hashtbl.find_exn candidate_rewards i)));
  (* find those productions that have enough weight to make it into the library *)
  let productions =
    (Hashtbl.to_alist candidate_rewards |>
     List.filter ~f:(fun (_,r) -> exp r > lambda) |> 
     List.map ~f:(fun (i,_) -> extract_expression dagger i)) @ 
    (snd g0 |> List.map ~f:fst |> List.filter ~f:is_terminal) in
  let new_grammar = make_flat_library productions in
  Printf.printf "Computed production rewards; keeping %i." (List.length productions);
  print_newline ();
(* productions |> List.iter (fun p -> print_string (string_of_expression p); print_newline ()); *)
  (* assembled corpus *)
  let corpus = merge_a_list ~f:lse @@ 
    List.map2_exn ~f:(fun task ->
        List.map ~f:(fun (i,l) -> ((i,task.task_type),l)))
      tasks task_posteriors in
  print_string "Assembled corpus."; print_newline ();
  (* fit the continuous parameters of the new grammar *)
  let likelihoods = program_likelihoods new_grammar dagger type_array requests in
  print_string "Computed likelihoods."; print_newline ();
  let final_grammar = fit_grammar smoothing new_grammar dagger type_array likelihoods corpus in
  print_string "Fit grammar."; print_newline ();
  (* check to see if we've hit a fixed point *)
  final_grammar
(*    let final_productions = snd final_grammar |> ExpressionMap.bindings
                          |> List.map fst |> List.sort compare_expression in
  let initial_productions = snd g0 |> ExpressionMap.bindings |> 
                            List.map fst |> List.sort compare_expression in
  if list_equal compare_expression final_productions initial_productions
  then final_grammar
  else final_grammar (* begin
    print_endline "Another compression iteration...";
    expectation_maximization_compress lambda smoothing final_grammar dagger 
      type_array requests candidates tasks program_scores
  end *)
    *)
  

let expectation_maximization_iteration prefix
    lambda smoothing frontier_size 
    tasks grammar = 
  let (frontiers,dagger) = enumerate_frontiers_for_tasks grammar frontier_size tasks in
  print_string "Scoring programs... \n";
  let program_scores = score_programs dagger frontiers tasks in
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
  let requests = List.fold_left frontiers
      ~init:Int.Map.empty ~f:(fun requests (requested_type,frontier) -> 
          List.fold_left frontier ~init:requests ~f:(fun (a : (tp list) Int.Map.t) (i : int) -> 
              match Int.Map.find a i with
	      | Some(old) -> 
	        if List.mem old requested_type then a 
                else Int.Map.add a ~key:i ~data:(requested_type::old)
              | None -> Int.Map.add a ~key:i ~data:[requested_type]))
  in
  (*  let grammar = make_flat_library @@ List.filter is_terminal @@ List.map fst @@ 
    ExpressionMap.bindings @@ snd grammar in *)
  let candidates = candidate_fragments dagger @@ List.map program_scores (List.map ~f:fst) in
  let final_grammar = expectation_maximization_compress lambda smoothing grammar dagger
      type_array requests candidates tasks program_scores in
  (* save the grammar *)
  Out_channel.write_all (prefix^"_grammar") ~data:(string_of_library final_grammar);
  print_newline ();
  final_grammar



let backward_iteration
    prefix lambda smoothing frontier_size keep_size
    tasks grammar = 
  let (dagger,frontiers) = make_frontiers frontier_size keep_size grammar tasks in
  let type_array = infer_graph_types dagger in  
  print_endline "Done inferring graph types.";
  let requests = List.fold2_exn ~f:(fun requests frontier t -> 
      let requested_type = t.task_type in
      List.fold_left ~f:(fun (a : (tp list) Int.Map.t) (i : int) -> 
          match Int.Map.find a i with
	  | Some(old) -> 
	    if List.mem old requested_type
	    then a else Int.Map.add a ~key:i ~data:(requested_type::old)
          | None -> Int.Map.add a ~key:i ~data:[requested_type]
	) ~init:requests frontier
    ) ~init:Int.Map.empty (List.map frontiers ~f:(List.map ~f:fst)) tasks
  in
  print_endline "Done getting requests.";
  let task_solutions = List.zip_exn tasks @@ 
    List.map frontiers (List.map ~f:(fun (i,_) -> (i,0.)))
  in
  (* the following lines are for running EM *)
  (* the commented outline afterwards will run lower bound refinement *)
  let solutions = List.map task_solutions ((List.map ~f:fst) % snd) in
  let candidates = candidate_fragments dagger solutions in
  let g = expectation_maximization_compress
      lambda smoothing grammar dagger type_array requests candidates tasks @@
    List.map task_solutions snd in
(*   let g = compress lambda smoothing dagger type_array requests task_solutions in *)
  (* save the grammar *)
  Out_channel.write_all (prefix^"_grammar") ~data:(string_of_library g);
  (* save the best programs *)
  let task_solutions = List.zip_exn tasks frontiers in
  save_best_programs (prefix^"_programs") dagger task_solutions;
  g
