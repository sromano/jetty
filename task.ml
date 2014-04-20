open Expression
open Type
open Enumerate
open Utils


type task = 
    { name : string; task_type : tp;
    score : expression -> float; };;


let enumerate_frontiers_for_tasks grammar frontier_size tasks 
    : (tp*int list) list*expressionGraph = 
  let types = remove_duplicates (List.map (fun t -> t.task_type) tasks) in
  Printf.printf "number of types: %i \n" (List.length types);
  let dagger = make_expression_graph 100000 in
  let indices = List.map (fun t -> enumerate_ID dagger grammar t frontier_size) types in
  (List.combine types 
  (List.map (compose (List.map fst) IntMap.bindings) indices),
   dagger);;


let score_programs dagger frontiers tasks = 
  List.map (fun task -> 
    List.filter (compose is_valid snd)
      (List.map (fun i -> 
	let e = extract_expression dagger i in
	(i,task.score e)
		) (List.assoc task.task_type frontiers))
	   ) tasks
;;
