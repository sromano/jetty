open Expression
open Type
open Utils


type task = 
    { name : string; task_type : tp;
    score : expression -> float; }


let score_programs dagger frontiers tasks = 
  List.map (fun task -> 
    List.filter (compose is_valid snd)
      (List.map (fun i -> 
	let e = extract_expression dagger i in
	(i,task.score e)
		) (List.assoc task.task_type frontiers))
	   ) tasks

