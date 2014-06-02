open Core.Std

open Expression
open Type
open Utils

type task_objective = 
  | LogLikelihood of (expression -> float)
  | Seed of expression

type task = 
    { name : string; task_type : tp;
    score : task_objective;
    proposal : ((expression -> float -> float) * (expression*float) list) option; }

let modify_grammar grammar t =
  let propose = fst @@ safe_get_some "modify_grammar propose" t.proposal 
  and extra = List.map (snd @@ safe_get_some "modify_grammar extra" t.proposal)
      ~f:(fun (e,w) -> (e,(w,infer_type e))) in
  let special_weights =
    extra @ List.map (snd grammar) (fun (e, (w,ty)) -> (e,(propose e w,ty))) in
  (fst grammar,special_weights)

let score_programs dagger frontiers tasks = 
  let start_time = time() in
  let scores = List.map tasks (fun task -> 
      let ll = match task.score with
      | Seed(_) -> raise (Failure "score_programs: task has seed")
      | LogLikelihood(ll) -> ll in
      List.filter ~f:(compose is_valid snd)
        (List.map ~f:(fun i -> 
             let e = extract_expression dagger i in
             (i,ll e)) (List.Assoc.find_exn frontiers task.task_type))) in
  let end_time = time() in
  Printf.printf "Scored programs in %f seconds." (end_time-.start_time); print_newline ();
  scores

let save_best_programs f dagger task_solutions = 
  let task_solutions = List.filter task_solutions (fun (_,s) -> List.length s > 0) in
  let s = String.concat ~sep:"\n" @@ List.map task_solutions (fun (t,s) ->
      let (e,p) = List.fold_left (List.tl_exn s) ~init:(List.hd_exn s) ~f:(fun (f,p) (g,q) -> 
          if p > q then (f,p) else (g,q))  in
      Printf.sprintf "%s\t%s\t%f" t.name (string_of_expression @@ extract_expression dagger e) p)
  in Out_channel.write_all f ~data:s
