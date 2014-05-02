(* Performs an iteration of exploration and compression using lower bound refinement *)

open Expression
open Type
open Task
open Library
open Enumerate
open Utils
open Compress


let lower_bound_refinement_iteration
    prefix lambda smoothing frontier_size 
    tasks grammar = 
  let (frontiers,dagger) = enumerate_frontiers_for_tasks grammar frontier_size tasks in
  print_string "Scoring programs...";
  print_newline ();
  let program_scores = score_programs dagger frontiers tasks in
  (* display the hit rate *)
  let number_hit = List.length (List.filter (fun scores -> 
    List.exists (fun (_,s) -> s > log (0.999)) scores
					    ) program_scores) in
  let number_of_partial = List.length (List.filter (fun scores -> 
    List.length scores > 0
						   ) program_scores) in
  Printf.printf "Hit %i / %i \n" number_hit (List.length tasks);
  Printf.printf "Partial credit %i / %i" (number_of_partial-number_hit) (List.length tasks);
  print_newline ();
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
  let task_solutions = List.filter (fun (_,s) -> List.length s > 0)
      (List.combine tasks @@ List.map (List.filter (fun (_,s) -> is_valid s)) program_scores)
  in
  let g = compress lambda smoothing dagger type_array requests task_solutions in
  let c = open_out (prefix^"_grammar") in
  Printf.fprintf c "%s" (string_of_library g);
  close_out c;
  g
