open Expression
open Type
open Task
open Library
open Enumerate
open Utils


let expectation_maximization_iteration
    lambda smoothing frontier_size 
    tasks grammar = 
  let (frontiers,dagger) = enumerate_frontiers_for_tasks grammar frontier_size tasks in
  print_string "Scoring programs... \n";
  let (i2n,_,_) = dagger in
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
  let likelihoods = program_likelihoods grammar dagger type_array requests in
  let task_posteriors = 
    List.map2 (fun task scores ->
      let scores = List.map (fun (i,s) -> (i,s+. Hashtbl.find likelihoods (i,task.task_type))) scores
      in let z = lse_list (List.map snd scores) in
      List.map (fun (i,s) -> (i,s-.z)) scores
	      ) tasks program_scores in
  (* compute rewards for each program *)
  let rewards = Hashtbl.create 100000 in
  List.iter (fun posterior -> 
    List.iter (fun (i,r) -> 
      try
	let old_reward = Hashtbl.find rewards i in
	Hashtbl.replace rewards i (old_reward+.(exp r))
      with Not_found -> Hashtbl.add rewards i (exp r)
	      ) posterior
	    ) task_posteriors;
  (* compute rewards for each expression *)
  let expression_rewards = Hashtbl.create 100000 in
  let reward_expression weight i =
    let rec reward j = 
      (try
	let old_reward = Hashtbl.find expression_rewards j in
	Hashtbl.replace expression_rewards j (old_reward+.weight)
      with Not_found -> Hashtbl.add expression_rewards j weight);
      match Hashtbl.find i2n j with
	ExpressionBranch(l,r) -> reward l; reward r
      | _ -> ()
    in reward i
  in Hashtbl.iter (fun i w -> reward_expression w i) rewards;
  (* find those productions that have enough weight to make it into the library *)
  let productions = List.map (fun (i,_) ->
    extract_expression dagger i) (List.filter (fun (i,r) -> 
       is_leaf_ID dagger i || r > lambda)
				    (hash_bindings expression_rewards)) in
  let new_grammar = make_flat_library productions in
  print_string "Computed posterior probabilities. \n";
  (* assembled corpus *)
  let corpus = List.map (fun (i,l) -> (i,exp l)) @@ merge_a_list lse @@ 
    List.map2 (fun task ->
      List.map @@ fun (i,l) -> ((i,task.task_type),l))
      tasks task_posteriors in
  (* fit the continuous parameters of the new grammar and then return it *)
  let likelihoods = program_likelihoods new_grammar dagger type_array requests in
  let final_grammar = fit_grammar smoothing new_grammar dagger type_array likelihoods corpus in
(*  print_string (string_of_library final_grammar); *)
  print_newline ();
  final_grammar
