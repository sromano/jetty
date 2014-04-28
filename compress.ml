open Expression
open Type
open Library
open Utils
open Task


let compress lambda dagger type_array requests (task_solutions : (task * (int*float) list) list) = 
  let (i2n,n2i,_) = dagger in
  let terminals = List.filter (fun (i,_) -> is_leaf_ID dagger i) (hash_bindings i2n) in
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
  let p = posterior @@ List.map fst terminals in
  ignore (for i = 1 to 50 do ignore (posterior @@ List.map fst terminals) done);
  let t2 = Sys.time () in
  (* about .05 sec for all likelihoods *)
  Printf.printf "time to compute posterior (%f) is %f \n" p (t2-.t1);
0;;

