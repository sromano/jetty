open Expression
open Type
open Library
open Utils
open Task


let compress lambda dagger type_array (task_solutions : (task * (int*float) list) list) = 
  let (i2n,n2i,_) = dagger in
  let terminals = List.filter (fun (i,_) -> is_leaf_ID dagger i) (hash_bindings i2n) in
  (* find the productions that are used in more than one task *)
  let task_uses = List.map (fun (_,solutions) -> 
    List.fold_left (fun a (i,_) -> 
      IntSet.union a (get_sub_IDs dagger i)
		   ) IntSet.empty solutions
			   ) task_solutions in
  let task_counts = List.fold_left (fun counts uses -> 
    IntSet.fold (fun i a -> 
      try
	let old_count = IntMap.find i a in
	IntMap.add i (old_count+1) a
      with Not_found -> IntMap.add i 1 a
		) uses counts
				   ) IntMap.empty task_uses in
  let candidates = List.filter (fun (i,c) -> c > 1 && not (is_leaf_ID dagger i)) (IntMap.bindings task_counts) in
  0
