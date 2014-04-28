open Expression
open Type
open Library
open Utils
open Task

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
	ExpressionLeaf(Terminal(t,_,_)) -> 
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
        [log @@ float_of_int @@ List.length @@ (terminals |> 
	List.filter (fun t -> can_unify type_array.(t) request))];
      candidate_conflicts := !candidate_conflicts @
	[List.map snd @@ (candidates |> List.filter
	  (fun (_,c) -> can_unify type_array.(c) request))];
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
  

let compress lambda dagger type_array requests (task_solutions : (task * (int*float) list) list) = 
  let (i2n,n2i,_) = dagger in
  let terminals = List.map fst @@ List.filter (fun (i,_) -> is_leaf_ID dagger i) (hash_bindings i2n) in
  (* Printf.printf "%i tasks solved by %i programs \n" (List.length task_solutions) (List.length @@ List.concat @@ List.map snd task_solutions); *)
  (* request might have spurious request for programs that don't solve any tasks *)
  (* Printf.printf "initial size of requests is %i \n" (IntMap.cardinal requests); *)
  let requests = requests |> IntMap.filter (fun i _ -> task_solutions |> 
  List.exists (fun (_,s) -> s |> List.exists (fun (j,_) -> j = i))) in
  (* Printf.printf "final size of requests is %i \n" (IntMap.cardinal requests); *)
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
  let dependencies = candidates |> List.map (fun i -> get_sub_IDs dagger i |> IntSet.filter (fun j -> List.mem j candidates)) in
  (* computes log posterior for a given subset of the candidates *)
  let posterior productions = 
    let production_expressions = List.map (extract_expression dagger) productions in
    let grammar = make_flat_library production_expressions in
    let likelihoods = program_likelihoods grammar dagger type_array requests in
    let log_prior = -.lambda *. (float_of_int @@ List.length productions) in
    task_solutions |> List.fold_left (fun ll (task,solutions) ->
      ll +. (solutions |> List.fold_left (fun a (i,l) ->
	lse a @@ l +. Hashtbl.find likelihoods (i,task.task_type)) neg_infinity)) log_prior
  in
  let t1 = Sys.time () in
  let p = posterior terminals in
  ignore (for i = 1 to 50 do ignore (posterior terminals) done);
  let t2 = Sys.time () in
  (* about .05 sec for all likelihoods *)
  Printf.printf "time to compute posterior (%f) is %f \n" p (t2-.t1);
0;;

