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
    List.map2 (fun task scores ->
        let scores = scores |> List.map (fun (i,s) -> 
            (i,s+. Hashtbl.find likelihoods (i,task.task_type)))  in
        let z = lse_list (List.map snd scores) in
        List.map (fun (i,s) -> (i,s-.z)) scores
      ) tasks program_scores in
  (* compute rewards for each expression *)
  let make_candidate_rewards () = 
    let r = Hashtbl.create 10000 in
    candidates |> List.iter (fun c -> Hashtbl.add r c neg_infinity);
    r
  in
  let candidate_likelihood = memorize (fun (c,r) -> 
    match likelihood_option g0 r @@ extract_expression dagger c with
    | None -> neg_infinity
    | Some(l) -> l) 10000 in
  let rec reward_expression candidate_rewards weight request i =
    match extract_node dagger i with
    | ExpressionBranch(l,r) -> 
      let left_request = function_request request in
      let right_request = argument_request request type_array.(l) in
      reward_expression candidate_rewards weight left_request l; 
      reward_expression candidate_rewards weight right_request r;
      (try
         let old = Hashtbl.find candidate_rewards i in
         Hashtbl.replace candidate_rewards i @@ lse old weight
       with Not_found -> (* Not a candidate - might still unify with some of them *)
         (if has_wildcards dagger i then
            let hits = List.filter (can_match_wildcards dagger i) candidates in
            if not (null hits) then (
              let likelihoods = List.map (fun hit -> candidate_likelihood (hit,request)) hits in
              let z = lse_list likelihoods in
              if z > neg_infinity then
                List.iter2 (fun h l -> Hashtbl.replace candidate_rewards h @@ 
                             lse (weight+.l-.z) @@ Hashtbl.find candidate_rewards h) 
                  hits likelihoods)))
    | _ -> ()
  in 
  let rewards = Array.make (List.length tasks) (Hashtbl.create 5) in
  let rewards = pmap ~processes:number_of_cores (fun (t,posterior) -> 
      let r = make_candidate_rewards () in
      List.iter (fun (i,w) -> reward_expression r w t.task_type i) posterior;
      r) (List.nth @@ List.combine tasks task_posteriors) rewards in
  let candidate_rewards = make_candidate_rewards () in
  Array.iter (Hashtbl.iter (fun i r -> 
    Hashtbl.replace candidate_rewards i @@ lse r @@ Hashtbl.find candidate_rewards i)) rewards;
  (* find those productions that have enough weight to make it into the library *)
  let productions =
    (hash_bindings candidate_rewards |>
     List.filter (fun (i,r) -> exp r > lambda) |> 
     List.map (fun (i,_) -> extract_expression dagger i)) @ 
    (snd g0 |> ExpressionMap.bindings |> List.map fst |> List.filter is_terminal) in
  let new_grammar = make_flat_library productions in
  Printf.printf "Computed production rewards; keeping %i." (List.length productions);
  print_newline ();
(* productions |> List.iter (fun p -> print_string (string_of_expression p); print_newline ()); *)
  (* assembled corpus *)
  let corpus = merge_a_list lse @@ 
    List.map2 (fun task ->
        List.map @@ fun (i,l) -> ((i,task.task_type),l))
      tasks task_posteriors in
  print_string "Assembled corpus."; print_newline ();
  (* fit the continuous parameters of the new grammar *)
  let likelihoods = program_likelihoods new_grammar dagger type_array requests in
  print_string "Computed likelihoods."; print_newline ();
  let final_grammar = fit_grammar smoothing new_grammar dagger type_array likelihoods corpus in
  print_string "Fit grammar."; print_newline ();
  (* check to see if we've hit a fixed point *)
  let final_productions = snd final_grammar |> ExpressionMap.bindings
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
    
  

let expectation_maximization_iteration prefix
    lambda smoothing frontier_size 
    tasks grammar = 
  let (frontiers,dagger) = enumerate_frontiers_for_tasks grammar frontier_size tasks in
  print_string "Scoring programs... \n";
  let program_scores = score_programs dagger frontiers tasks in
  (* display the hit rate *)
  let number_hit = List.length (List.filter (fun scores -> 
      List.exists (fun (_,s) -> s > log (0.999)) scores
    ) program_scores) in
  let number_of_partial = List.length (List.filter (fun scores -> 
      List.length scores > 0
    ) program_scores) in
  Printf.printf "Hit %i / %i \n" number_hit (List.length tasks);
  Printf.printf "Partial credit %i / %i \n" (number_of_partial-number_hit) (List.length tasks);
  (* compute likelihoods under grammar and then normalize the frontiers *)
  let type_array = infer_graph_types dagger in  
  let requests = List.fold_left (fun requests (requested_type,frontier) -> 
      List.fold_left (fun (a : (tp list) IntMap.t) (i : int) -> 
          try
	    let old = IntMap.find i a in
	    if List.mem requested_type old
	    then a else IntMap.add i (requested_type::old) a
          with Not_found -> IntMap.add i [requested_type] a
	) requests frontier
    ) IntMap.empty frontiers
  in
(*  let grammar = make_flat_library @@ List.filter is_terminal @@ List.map fst @@ 
    ExpressionMap.bindings @@ snd grammar in *)
  let candidates = candidate_fragments dagger @@ List.map (List.map fst) program_scores in
  let final_grammar = expectation_maximization_compress lambda smoothing grammar dagger
      type_array requests candidates tasks program_scores in
  (* save the grammar *)
  let c = open_out (prefix^"_grammar") in
  Printf.fprintf c "%s" (string_of_library final_grammar);
  close_out c;
  print_newline ();
  final_grammar



let backward_iteration
    prefix lambda smoothing frontier_size keep_size
    tasks grammar = 
  let dagger = make_expression_graph 100000 in
  print_endline "Generating backward rewrites...";
  let rewrites = snd grammar |> ExpressionMap.bindings |> List.map (fun (e,(_,t)) -> 
      (* load primitives into the graph *)
      ignore(insert_expression dagger e);
      get_templates e t |> List.map (fun (target,template) -> (template,apply_template target)))
                 |> List.concat in
  let frontiers = tasks |> List.map (fun t -> 
    Printf.printf "Enumerating (backwards) for %s" t.name;
    print_newline ();
    let i = insert_expression dagger @@ match t.score with
      | Seed(s) -> s
      | LogLikelihood(_) -> raise (Failure "backward_iteration: task has no seed") in
    let f = backward_enumerate dagger grammar rewrites frontier_size keep_size t.task_type i in
    print_endline "\nFinished enumerating."; f) in
  let type_array = infer_graph_types dagger in  
  print_endline "Done inferring graph types.";
  let requests = List.fold_left2 (fun requests frontier t -> 
      let requested_type = t.task_type in
      List.fold_left (fun (a : (tp list) IntMap.t) (i : int) -> 
          try
	    let old = IntMap.find i a in
	    if List.mem requested_type old
	    then a else IntMap.add i (requested_type::old) a
          with Not_found -> IntMap.add i [requested_type] a
	) requests frontier
    ) IntMap.empty (List.map (List.map snd) frontiers) tasks
  in
  print_endline "Done getting requests.";
  let task_solutions = List.combine tasks @@ 
    List.map (List.map (fun (_,i) -> (i,0.))) frontiers
  in
  (* the following lines are for running EM *)
  (* the commented outline afterwards will run lower bound refinement *)
  let solutions = List.map (compose (List.map fst) snd) task_solutions in
  let candidates = candidate_fragments dagger solutions in
  let g = expectation_maximization_compress
      lambda smoothing grammar dagger type_array requests candidates tasks @@
    List.map snd task_solutions in
(*   let g = compress lambda smoothing dagger type_array requests task_solutions in *)
  (* save the grammar *)
  let c = open_out (prefix^"_grammar") in
  Printf.fprintf c "%s" (string_of_library g);
  close_out c;
  (* save the best programs *)
  let task_solutions = List.combine tasks (List.map (List.map (fun (l,i) -> (i,l))) frontiers) in
  save_best_programs (prefix^"_programs") dagger task_solutions;
  g
