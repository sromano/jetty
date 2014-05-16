open Expression
open Type
open Library
open Utils
open Task
open Bottom_up


(* finds all of the fragments we might consider adding to the grammar
this can handle the case when the programs have wildcards in them 
the fragments we consider adding should never have wildcards in them
a fragment without wildcards is included when it occurs in a different task,
possibly with wildcards.
if 2 fragments from different tasks unify to a grounded expression,
that grounded expression gets included as a fragment.
*)
let candidate_fragments dagger solutions = 
  (* for each task, collect up all the fragments into a set *)
  let fragments = solutions |> List.map (IntSet.empty |> List.fold_left (fun a i -> 
    IntSet.union a @@ get_sub_IDs dagger i)) in
  (* record candidates in place *)
  let candidates = Hashtbl.create 10000 in
  let rec get_fragments head_task other_tasks = 
    try (* next 2 lines will throw exception once we're done *)
      let next_head = List.hd other_tasks
      and next_tail = List.tl other_tasks in
      (* loop over every solution to the head task;
         collect up the fragments and check to see if they should be included *)
      head_task |> IntSet.iter (fun fragment -> 
          if Hashtbl.mem candidates fragment then () else 
          let wild = has_wildcards dagger fragment in
          other_tasks |> List.iter (IntSet.iter (fun other_fragment -> 
              if wild || has_wildcards dagger other_fragment
              then match combine_wildcards dagger fragment other_fragment with
                | Some(union_fragment) when (not (Hashtbl.mem candidates union_fragment)
                                             && not (has_wildcards dagger union_fragment)) -> 
                  Hashtbl.add candidates union_fragment true
                | _ -> ()
              else if fragment = other_fragment && not (Hashtbl.mem candidates fragment)
                        then Hashtbl.add candidates fragment true
            )));
      get_fragments next_head next_tail
    with _ -> () (* no more tasks *)
  in 
  get_fragments (List.hd fragments) (List.tl fragments);
  hash_bindings candidates |> List.map fst
    

let compute_job_IDs dagger type_array terminals candidates requests =
  let (i2n,_,_) = dagger in
  (* number all of the candidates *)
  let candidates = candidates |> List.mapi (fun i c -> (c,i)) in
  (* maps tuples of (ID,request) to job ID *)
  let jobs = Hashtbl.create 10000 in
  (* these lists contain information about the jobs *)
  let candidate_index = ref [] in
  let has_children = ref [] in
  let left_child = ref [] in
  let right_child = ref [] in
  let terminal_conflicts = ref [] in
  let candidate_conflicts = ref [] in
  let rec make_job i request = 
    try
      Hashtbl.find jobs (i,request) 
    with Not_found -> 
      (match Hashtbl.find i2n i with
        ExpressionLeaf(Terminal(_,_,_)) -> 
          has_children := !has_children @ [false];
          left_child := !left_child @ [0];
          right_child := !right_child @ [0]
      | ExpressionLeaf(_) -> raise (Failure "leaf not terminal")
      | ExpressionBranch(l,r) -> 
          let left_request = canonical_type (make_arrow (TID(next_type_variable request)) request) in
          let right_request = argument_request request type_array.(l) in
          let left_job = make_job l left_request in
          let right_job = make_job r right_request in
          has_children := !has_children @ [true];
          left_child := !left_child @ [left_job];
          right_child := !right_child @ [right_job]);
      candidate_index := !candidate_index @
        [try List.assoc i candidates with _ -> -1];
      terminal_conflicts := !terminal_conflicts @
        [float_of_int @@ List.length @@ (terminals |> 
        List.filter (fun t -> can_unify type_array.(t) request))];
      candidate_conflicts := !candidate_conflicts @
        [List.map snd @@ (candidates |> List.filter
                            (fun (c,_) -> can_unify type_array.(c) request))
        ];
      let j = Hashtbl.length jobs in
      Hashtbl.add jobs (i,request) j;
      j
  in
  (* create a job for each request and all of its sub requests *)
  ignore(requests |> IntMap.iter (fun i types -> types |> 
  List.iter (fun t -> ignore(make_job i t))));
  (* pack everything up into arrays and then return it all *)
  (Array.of_list !candidate_index,
   Array.of_list !has_children,
   Array.of_list !left_child,
   Array.of_list !right_child,
   Array.of_list !terminal_conflicts,
   Array.of_list !candidate_conflicts,
   jobs)
  

let compress lambda smoothing dagger type_array requests (task_solutions : (task * (int*float) list) list) = 
  let t1 = Sys.time () in
  let (i2n,n2i,_) = dagger in
  let terminals = List.map fst @@ List.filter (fun (i,_) -> is_leaf_ID dagger i) (hash_bindings i2n) in
  (* request might have spurious request for programs that don't solve any tasks *)
  let requests = requests |> IntMap.filter (fun i _ -> task_solutions |> 
  List.exists (fun (_,s) -> s |> List.exists (fun (j,_) -> j = i))) in
  (* find the productions that are used in more than one task *)
  let task_uses = task_solutions |> List.map (fun (_,solutions) -> 
    solutions |> List.fold_left (fun a (i,_) -> 
      IntSet.union a @@ get_sub_IDs dagger i
                                ) IntSet.empty 
                                             ) in
  let task_counts = List.fold_left (fun counts uses -> 
    IntSet.fold (fun i a -> 
      try
        let old_count = IntMap.find i a in
        IntMap.add i (old_count+1) a
      with Not_found -> IntMap.add i 1 a
                ) uses counts
                                   ) IntMap.empty task_uses in
  let candidates = List.map fst (IntMap.bindings task_counts |> List.filter (fun (i,c) -> c > 1 && not (is_leaf_ID dagger i))) in
  Printf.printf "Found %i candidate productions \n" (List.length candidates);
  (* compute the dependencies of each candidate *)
  let dependencies =
    Array.of_list (candidates
                   |> List.map (fun i ->
                       let children = IntSet.elements @@ get_sub_IDs dagger i in
                       let children = children |> List.filter (fun j -> List.mem j candidates) in
                       children |> List.map (index_of candidates))) in
  (* precompute all of the typing information *)
  let (candidate_index,has_children,
       left_child,right_child,
       terminal_conflicts,candidate_conflicts,
       jobs) = compute_job_IDs dagger type_array terminals candidates requests
  in
  (* figure out correspondence between jobs and tasks *)
  let task_jobs = List.map (fun (task,solutions) -> 
                           List.map (fun (i,l) -> 
                             (Hashtbl.find jobs (i,task.task_type), l)
                                    ) solutions
                           ) task_solutions in
  (* routine for performing the dynamic program *)
  let number_jobs = Hashtbl.length jobs in
  let job_likelihoods = Array.make number_jobs 0. in
  let do_jobs productions = 
    for j = 0 to (number_jobs-1) do
      let application = 
        if has_children.(j)
        then -.log2 +. 
            job_likelihoods.(left_child.(j)) +.
            job_likelihoods.(right_child.(j))
        else neg_infinity
      in let terminal =
        if not has_children.(j) || 
            (candidate_index.(j) > -1 && productions.(candidate_index.(j)))
        then -.log2 -.
            log (List.fold_left (fun a k -> 
              if productions.(k) then a+.1. else a
                                ) terminal_conflicts.(j) candidate_conflicts.(j))
        else neg_infinity
      in job_likelihoods.(j) <- lse application terminal
    done
  in
  (* computes log posterior for a given subset of the candidates *)
  let posterior productions = 
    let log_prior = -.lambda *. Array.fold_left 
        (fun a u -> if u then a+.1. else a) 0. productions in
    let likelihood = List.fold_left (fun a t -> 
      let ls = List.map (fun (j,l) -> l +. job_likelihoods.(j)) t in
      a +. lse_list ls) 0. task_jobs in
    log_prior +. likelihood
  in
  (* computes the state successors in the search space *)
  let successors productions =
    let new_productions = 0--(List.length candidates - 1) |> 
    List.filter (fun p -> not productions.(p)) 
    in List.map (fun p -> 
                let a = Array.copy productions in
                a.(p) <- true;
                List.iter (fun q -> a.(q) <- true) @@ dependencies.(p);
                a) new_productions
  in
  (* performs a greedy search *)
  let rec hill_climb productions = 
    do_jobs productions;
    let current_score = posterior productions in
    let new_scores = successors productions |> List.map (fun s -> do_jobs s; (posterior s, s)) in
    if List.length new_scores > 0
    then let (new_score,new_productions) = 
      List.fold_left (fun (s1,p1) (s2,p2) -> if s1 > s2 then (s1,p1) else (s2,p2))
        (List.hd new_scores) (List.tl new_scores) in
      if new_score > current_score
      then hill_climb new_productions
      else productions
    else productions
  in
  let t2 = Sys.time () in
  Printf.printf "time to prepare for hillclimbing is %f" (t2-.t1);
  print_newline ();
  Printf.printf "about to begin hillclimbing..."; print_newline ();
  let t1 = Sys.time () in
  let initial_state = Array.make (List.length candidates) false in
  let productions = hill_climb initial_state in
  let es = List.map (extract_expression dagger) @@
    terminals @ (List.map fst @@ 
                 List.filter (fun (_,i) -> productions.(i)) @@ 
                 List.mapi (fun i c -> (c,i)) candidates) in
  let new_grammar = fit_grammar_to_tasks smoothing (make_flat_library es) 
    dagger type_array requests task_solutions in
  let t2 = Sys.time () in
  Printf.printf "time to compute grammar is %f \n " (t2-.t1);
  new_grammar

