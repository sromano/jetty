open Library
open Expression
open Type
open Utils
open Task

let enumerate_bounded dagger (log_application,distribution) rt bound = 
  let log_terminal = log (1.0-. exp log_application) in
  let terminals = List.map (fun (e,l) ->
    (infer_type e,(insert_expression dagger e, l)))
      (ExpressionMap.bindings distribution) in
  let type_blacklist = [c_S;c_B;c_C;c_K;c_I] |> List.map terminal_type in
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
                if List.mem my_type type_blacklist
                then acc2 
                else add_node acc2 application (arg_l+.fun_l+.log_application) my_type
                            ) acc (IntMap.bindings xs)
                          ) IntMap.empty (IntMap.bindings fs)
    in
    let availableTerminals = terminals |> List.filter (fun (t,(e,_)) -> 
        can_unify t requestedType && (can_identify || e <> identity_ID)) in
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
    then iterate (bound+.0.4)
    else
      (Printf.printf "Type %s \t Bound %f \t  => %i / %i programs \n" (string_of_type t) bound (IntMap.cardinal indices) frontier_size;
       indices)
  in iterate (log (float_of_int frontier_size))


let enumerate_frontiers_for_tasks grammar frontier_size tasks 
    : (tp*int list) list*expressionGraph = 
  let types = remove_duplicates (List.map (fun t -> t.task_type) tasks) in
  Printf.printf "number of types: %i \n" (List.length types);
  let dagger = make_expression_graph 100000 in
  let indices = List.map (fun t -> enumerate_ID dagger grammar t frontier_size) types in
  (List.combine types 
  (List.map (compose (List.map fst) IntMap.bindings) indices),
   dagger)



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
