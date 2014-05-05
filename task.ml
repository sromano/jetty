open Expression
open Type
open Utils

type task = 
    { name : string; task_type : tp;
    score : expression -> float;
    proposal : (expression -> float -> float) option; }


let score_programs dagger frontiers tasks = 
  let start_time = Sys.time() in
  let scores = List.map (fun task -> 
      List.filter (compose is_valid snd)
        (List.map (fun i -> 
             let e = extract_expression dagger i in
             (i,task.score e)
           ) (List.assoc task.task_type frontiers))
    ) tasks in
  let end_time = Sys.time() in
  Printf.printf "Scored programs in %f seconds." (end_time-.start_time); print_newline ();
  scores

let save_best_programs f dagger task_solutions = 
  let task_solutions = task_solutions |> List.filter (fun (_,s) -> List.length s > 0) in
  let s = String.concat "\n" @@ List.map
          (fun (t,s) -> let (e,p) = List.tl s |> List.fold_left (fun (f,p) (g,q) -> 
                if p > q then (f,p) else (g,q)) (List.hd s) in
            Printf.sprintf "%s\t%s\t%f" t.name (string_of_expression @@ extract_expression dagger e) p)
          task_solutions 
  in let c = open_out f in
  Printf.fprintf c "%s" s;
  close_out c
