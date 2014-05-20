open Library
open Expression
open Type
open Utils
open Task


let reduce_symmetries = false


let enumerate_bounded dagger (log_application,distribution) rt bound = 
  let log_terminal = log (1.0-. exp log_application) in
  let terminals = List.map (fun (e,(l,t)) ->
    (t,(insert_expression dagger e, l)))
      (ExpressionMap.bindings distribution) in
  let type_blacklist = TID(0) :: ([c_S;c_B;c_C;c_K;c_I] |> List.map terminal_type) in
  let identity_ID = insert_expression dagger c_I in
  let rec enumerate can_identify requestedType budget = 
    let add_node acc e l c = 
      try
        let (other_l,other_context) = IntMap.find e acc in
        if l > other_l
        then IntMap.add e (l,c) acc
        else acc
      with Not_found -> IntMap.add e (l,c) acc
    in
    let applications = 
      if budget < -.log_application
      then IntMap.empty
      else let f_request = make_arrow (TID(next_type_variable requestedType)) requestedType in
           let fs = enumerate false f_request (budget+.log_application) in
           List.fold_left (fun acc (f,(fun_l,fun_type)) -> 
            let x_request = argument_request requestedType fun_type in
            let xs = enumerate true x_request (budget+.log_application+.fun_l) in
             List.fold_left (fun acc2 (x,(arg_l,arg_type)) -> 
                let application = insert_expression_node dagger (ExpressionBranch(f,x)) in
                let my_type = application_type fun_type arg_type in
                if reduce_symmetries && List.mem my_type type_blacklist
                then acc2 
                else add_node acc2 application (arg_l+.fun_l+.log_application) my_type
                            ) acc (IntMap.bindings xs)
                          ) IntMap.empty (IntMap.bindings fs)
    in
    let availableTerminals = terminals |> List.filter (fun (t,(e,_)) -> 
        can_unify t requestedType && (not (reduce_symmetries) || can_identify || e <> identity_ID)) in
    match availableTerminals with
      [] -> applications
    | _ ->
        let z = lse_list (List.map (fun (_,(_,l)) -> l) availableTerminals) in
        let availableTerminals = List.map (fun (t,(e,l)) -> (t,(e,l-.z))) availableTerminals in
        let availableTerminals = List.filter (fun (t,(_,l)) -> 0.0-.log_terminal-.l < budget) availableTerminals in
        List.fold_left (fun acc (t,(e,l)) -> 
          add_node acc e (log_terminal+.l) t) applications availableTerminals
  in IntMap.map fst (enumerate true rt bound)


(* iterative deepening version of enumerate_bounded *)
let enumerate_ID dagger library t frontier_size = 
  let rec iterate bound = 
    let indices = enumerate_bounded dagger library t bound in
    if (IntMap.cardinal indices) < frontier_size
    then iterate (bound+.0.5)
    else
      (Printf.printf "Type %s \t Bound %f \t  => %i / %i programs" (string_of_type t) bound (IntMap.cardinal indices) frontier_size;
       print_newline ();
       IntMap.bindings indices |> List.sort 
         (fun (_,p) (_,q) -> compare q p) |> take frontier_size)
  in iterate (1.3 *. log (float_of_int frontier_size))


let enumerate_frontiers_for_tasks grammar frontier_size tasks 
    : (tp*int list) list*expressionGraph = 
  let start_time = Sys.time() in
  let (special_tasks,normal_tasks) = List.partition (fun t -> is_some @@ t.proposal) tasks in
  let types = remove_duplicates (List.map (fun t -> t.task_type) tasks) in
  Printf.printf "number of (normal) types: %i \n" (List.length types);
  let dagger = make_expression_graph 100000 in
  let indices = List.map (fun t -> enumerate_ID dagger grammar t frontier_size) types in
  let special_indices = special_tasks |> List.map (fun t -> 
      Printf.printf "Enumerating for task \"%s\"" t.name; print_newline ();
      let special_weights =
        ExpressionMap.mapi (fun e (w,ty) -> (get_some t.proposal e w,ty)) (snd grammar) in
      let special_grammar = (fst grammar,special_weights) in
      let special_indices = enumerate_ID dagger special_grammar t.task_type frontier_size in
      (t.task_type, List.fold_left (fun s i -> IntSet.add i s) IntSet.empty @@ 
       List.map fst special_indices)) in
  let end_time = Sys.time() in
  Printf.printf "Enumerated all programs in %f seconds." (end_time-.start_time);
  print_newline ();
  let start_time = Sys.time() in
  let indices = List.combine types @@ 
    List.map (fun iDs -> List.fold_left (fun s i -> IntSet.add i s) IntSet.empty @@ 
               List.map fst iDs) indices in
  (* combines special indices with normal indices *)
  let indices = special_indices |> List.fold_left (fun i (ty,j) -> 
      i |> List.map (fun (ty2,j2) -> if ty = ty2
                    then (ty2,IntSet.union j j2)
                    else (ty2,j2))
    ) indices in
  let number_of_programs = indices |> List.map snd |> List.fold_left IntSet.union IntSet.empty |> 
                           IntSet.cardinal in
  let end_time = Sys.time() in
  Printf.printf "Coalesced %i programs in %f seconds." number_of_programs (end_time-.start_time);
  print_newline ();
  (indices |> List.map (fun (t,s) -> (t,IntSet.elements s)), dagger)



let test_enumerate () = 
  let dagger = make_expression_graph 10000 in
  let indices = enumerate_bounded dagger polynomial_library (make_arrow tint tint) 11.49 in
  let type_array = infer_graph_types dagger in
  let requests = IntMap.map (fun _ -> [(make_arrow tint tint)]) indices in
  let ls = program_likelihoods polynomial_library dagger type_array requests in
  let through = List.map (fun (e,_) -> ((Hashtbl.find ls (e,make_arrow tint tint)),(extract_expression dagger e))) (IntMap.bindings indices )
  in let kansas = List.sort (fun (l,_) (r,_) -> compare l r) through in
  print_string (String.concat "\n" (List.map (fun (l,e) -> 
    string_of_expression  e ^ "\t" ^ string_of_float l)
                                    kansas  ))

 (* test_enumerate ();; *)
