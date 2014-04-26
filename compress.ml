open Expression
open Type
open Library
open Utils

let compress lambda dagger type_array (task_solutions : task*(int*float list) list) = 
  let (i2n,n2i,_) = dagger in
  let terminals = List.filter (fun (i,_) -> is_leaf_ID dagger i) (hash_bindings i2n) in
  (* find the productions that are used in more than one task *)
  let task_uses = List.map (fun (_,solutions) -> 
    let  = in
			   ) task_solutions
  in
