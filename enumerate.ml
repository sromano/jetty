open Core.Std

open Library
open Expression
open Type
open Utils
open Task


let reduce_symmetries = true


let enumerate_bounded dagger (log_application,distribution) rt bound = 
  let log_terminal = log (1.0-. exp log_application) in
  let terminals = List.map distribution (fun (e,(l,t)) ->
    (t,(insert_expression dagger e, l))) in
  let type_blacklist = TID(0) :: ([c_S;c_B;c_C;c_K;c_I] |> List.map ~f:terminal_type) in
  let identity_ID = insert_expression dagger c_I in
  let rec enumerate can_identify requestedType budget = 
    let add_node acc e l c = 
      try
        let (other_l,other_context) = Int.Map.find_exn acc e in
        if l > other_l
        then Int.Map.add acc e (l,c)
        else acc
      with Not_found -> Int.Map.add acc e (l,c)
    in
    let applications = 
      if budget < -.log_application
      then Int.Map.empty
      else let f_request = make_arrow (TID(next_type_variable requestedType)) requestedType in
           let fs = enumerate false f_request (budget+.log_application) in
           List.fold_left (Int.Map.to_alist fs) ~init:Int.Map.empty
             ~f:(fun acc (f,(fun_l,fun_type)) -> 
                 let x_request = argument_request requestedType fun_type in
                 let xs = enumerate true x_request (budget+.log_application+.fun_l) in
                 List.fold_left (Int.Map.to_alist xs) ~init:acc
                   ~f:(fun acc2 (x,(arg_l,arg_type)) -> 
                       let application = insert_expression_node dagger (ExpressionBranch(f,x)) in
                       let my_type = application_type fun_type arg_type in
                       if reduce_symmetries && List.mem type_blacklist my_type
                       then acc2 
                       else add_node acc2 application (arg_l+.fun_l+.log_application) my_type))
    in
    let availableTerminals = List.filter terminals (fun (t,(e,_)) -> 
        can_unify t requestedType && (not (reduce_symmetries) || can_identify || e <> identity_ID)) in
    match availableTerminals with
      [] -> applications
    | _ ->
        let z = lse_list (List.map availableTerminals (fun (_,(_,l)) -> l)) in
        let availableTerminals = List.map availableTerminals (fun (t,(e,l)) -> (t,(e,l-.z))) in
        let availableTerminals = List.filter availableTerminals (fun (t,(_,l)) -> 0.0-.log_terminal-.l < budget) in
        List.fold_left availableTerminals ~init:applications ~f:(fun acc (t,(e,l)) -> 
          add_node acc e (log_terminal+.l) t)
  in Int.Map.map (enumerate true rt bound) fst


(* iterative deepening version of enumerate_bounded *)
let enumerate_ID dagger library t frontier_size = 
  let rec iterate bound = 
    let indices = enumerate_bounded dagger library t bound in
    if (Int.Map.length indices) < frontier_size
    then begin
      Printf.printf "Type %s \t Bound %f \t  => %i / %i programs"  (string_of_type t) bound (Int.Map.length indices) frontier_size;
      print_newline ();
      iterate (bound+.0.5)
    end
    else
      (Printf.printf "Type %s \t Bound %f \t  => %i / %i programs" (string_of_type t) bound (Int.Map.length indices) frontier_size;
       print_newline ();
       Int.Map.to_alist indices |> List.sort 
         ~cmp:(fun (_,p) (_,q) -> compare q p) |> Fn.flip List.take frontier_size)
  in iterate (1.3 *. log (Float.of_int frontier_size))


let enumerate_frontiers_for_tasks grammar frontier_size tasks 
    : (tp*int list) list*expressionGraph = 
  let start_time = time () in
  let (special_tasks,normal_tasks) = List.partition_tf tasks (fun t -> is_some @@ t.proposal) in
  let types = remove_duplicates (List.map tasks (fun t -> t.task_type)) in
  Printf.printf "number of (normal) types: %i \n" (List.length types);
  let dagger = make_expression_graph 100000 in
  let indices = List.map types (fun t -> enumerate_ID dagger grammar t frontier_size) in
  let special_indices = List.map special_tasks (fun t -> 
      Printf.printf "Enumerating for task \"%s\"" t.name; print_newline ();
      let special_weights =
        List.map (snd grammar) (fun (e, (w,ty)) -> (e,(get_some t.proposal e w,ty))) in
      let special_grammar = (fst grammar,special_weights) in
      let special_indices = enumerate_ID dagger special_grammar t.task_type frontier_size in
      (t.task_type, List.fold_left (List.map special_indices fst)
         ~f:Int.Set.add ~init:Int.Set.empty)) in
  let end_time = time () in
  Printf.printf "Enumerated all programs in %f seconds." (end_time-.start_time);
  print_newline ();
  let start_time = time() in
  let indices = List.zip_exn types @@ 
    List.map indices (fun iDs -> 
        List.fold_left (List.map iDs fst) ~init:Int.Set.empty ~f:Int.Set.add) in
  (* combines special indices with normal indices *)
  let indices = List.fold_left special_indices ~f:(fun i (ty,j) -> 
      i |> List.map ~f:(fun (ty2,j2) -> if ty = ty2
                         then (ty2,Int.Set.union j j2)
                         else (ty2,j2))) ~init:indices in
  let number_of_programs = indices |> List.map ~f:snd |> 
                           List.fold_left ~f:Int.Set.union ~init:Int.Set.empty |> 
                           Int.Set.length in
  let end_time = time() in
  Printf.printf "Coalesced %i programs in %f seconds." number_of_programs (end_time-.start_time);
  print_newline ();
  (indices |> List.map ~f:(fun (t,s) -> (t,Int.Set.to_list s)), dagger)



let test_enumerate () = 
  let dagger = make_expression_graph 10000 in
  let indices = enumerate_bounded dagger polynomial_library (make_arrow tint tint) 11.49 in
  let type_array = infer_graph_types dagger in
  let requests = Int.Map.map indices (fun _ -> [(make_arrow tint tint)]) in
  let ls = program_likelihoods polynomial_library dagger type_array requests in
  let through = List.map (Int.Map.to_alist indices)
      (fun (e,_) -> ((Hashtbl.find_exn ls (e,make_arrow tint tint)),(extract_expression dagger e)))
  in let kansas = List.sort (fun (l,_) (r,_) -> compare l r) through in
  print_string (String.concat ~sep:"\n" (List.map ~f:(fun (l,e) -> 
    string_of_expression  e ^ "\t" ^ Float.to_string l)
                                    kansas  ))

 (* test_enumerate ();; *)
