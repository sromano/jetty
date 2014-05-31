open Core.Std

open Library
open Task
open Enumerate
open Bottom_up
open Expression
open Utils
open Expression

(* wrapper over various enumeration and scoring functions *)
(* returns a list of frontiers, one for each task *)
(* each frontier is a list of tuples of (expression ID,score) *)
(* for bottom-up, score is log prior; for top-down, its likelihood *)
(* also returns an expression graph *)
let make_frontiers size keep_size grammar tasks = 
  let (bottom_tasks,top_tasks) = List.partition_tf tasks (fun t -> 
      match t.score with
      | Seed(_) -> true
      | LogLikelihood(_) -> false) in
  let (dagger,top_program_scores) = 
    if List.is_empty (top_tasks)
    then (make_expression_graph 100000,[])
    else 
      let (top_frontiers, dagger) = enumerate_frontiers_for_tasks grammar size tasks in
      let top_program_scores = score_programs dagger top_frontiers tasks in
      (* display the hit rate *)
      begin
        let number_hit = List.length (List.filter top_program_scores (fun scores -> 
            List.exists scores (fun (_,s) -> s > log (0.999)))) in
        let number_of_partial = List.length (List.filter ~f:(fun scores -> 
            List.length scores > 0
          ) top_program_scores) in
        Printf.printf "Hit %i / %i \n" number_hit (List.length top_tasks);
        Printf.printf "Partial credit %i / %i" (number_of_partial-number_hit)
          (List.length top_tasks);
        print_newline ();
        (dagger, top_program_scores)
      end
  in let bottom_program_scores = 
    if List.is_empty (bottom_tasks)
    then []
    else begin
      print_endline "Generating backward rewrites...";
      let rewrites = snd grammar |> List.map ~f:(fun (e,(_,t)) -> 
          (* load primitives into the graph *)
          ignore(insert_expression dagger e);
          get_templates e t |> List.map ~f:(fun (target,template) -> 
              (template,apply_template target))) |> List.concat in
      if number_of_cores = 1 then
        List.map bottom_tasks (fun t -> 
            Printf.printf "Enumerating (backwards) for %s..." t.name;
            print_newline ();
            let i = insert_expression dagger @@ match t.score with
              | Seed(s) -> s
              | LogLikelihood(_) -> raise (Failure "make_frontiers: task has no seed") in
            backward_enumerate dagger grammar rewrites size keep_size t.task_type i)
      else (* parallel bottom-up enumeration *)
        let graphs_and_frontiers = 
          Array.create (List.length bottom_tasks) (make_expression_graph 10,[]) in
        let graphs_and_frontiers = 
          pmap ~processes:number_of_cores (fun t ->
              let temp_dagger = make_expression_graph 10000 in
              let i = insert_expression temp_dagger @@ match t.score with
                | Seed(s) -> s
                | LogLikelihood(_) -> raise (Failure "make_frontiers: partask has no seed") in
              let f = backward_enumerate temp_dagger grammar rewrites size keep_size t.task_type i in
              scrub_graph temp_dagger;
              (temp_dagger,f))
            (List.nth_exn bottom_tasks) graphs_and_frontiers in
        Array.to_list graphs_and_frontiers |> List.map ~f:(fun (g,f) -> 
            dirty_graph g;
            List.map f (fun (i,l) -> (insert_expression dagger @@ extract_expression g i,l)))
    end
  in 
  (* coalesced top and bottom *)
  let bottom = ref bottom_program_scores 
  and top = ref top_program_scores in
  let fs = List.map tasks (fun t -> 
      let f = match t.score with
        | Seed(_) -> bottom
        | LogLikelihood(_) -> top in
      let x = List.hd_exn !f in
      f := List.tl_exn !f;
      x)
  in (dagger, fs)
