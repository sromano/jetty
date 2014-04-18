open Library
open Expression
open Type
open Utils

let enumerate_bounded (log_application,distribution) rt bound = 
  let log_terminal = log (1.0-. exp log_application) in
  let terminals = List.map (fun (e,l) -> (infer_type e,(e,l))) (ExpressionMap.bindings distribution) in
  let rec enumerate context requestedType budget = 
    let add_node acc e l c = 
      try
	let (other_l,other_context) = ExpressionMap.find e acc in
	if l > other_l
	then ExpressionMap.add e (l,c) acc
	else acc
      with Not_found -> ExpressionMap.add e (l,c) acc
    in
    let applications = 
      if budget < -.log_application
      then ExpressionMap.empty
      else let (xt,c2) = makeTID context in
           let fs = enumerate c2 (make_arrow xt requestedType) (budget+.log_application) in
	   List.fold_left (fun acc (f,(fun_l,fun_context)) -> 
	     let (xt2,c3) = chaseType fun_context xt in
	     let xs = enumerate c3 xt2 (budget+.log_application+.fun_l) in
	     List.fold_left (fun acc2 (x,(arg_l,arg_context)) -> 
	       add_node acc2 (make_app f x) (arg_l+.fun_l+.log_application) arg_context
			    ) acc (ExpressionMap.bindings xs)
			  ) ExpressionMap.empty (ExpressionMap.bindings fs)
    in
    let availableTerminals = List.filter (fun (t,_) -> can_unify t requestedType) terminals in
    match availableTerminals with
      [] -> applications
    | _ ->
	let z = lse_list (List.map (fun (_,(_,l)) -> l) availableTerminals) in
	let availableTerminals = List.map (fun (t,(e,l)) -> (t,(e,l-.z))) availableTerminals in
	let availableTerminals = List.filter (fun (t,(e,l)) -> 0.0-.log_terminal-.l < budget) availableTerminals in
	List.fold_left (fun acc (t,(e,l)) -> 
	  let (t,context1) = instantiate_type context t in
	  let context2 = unify context1 t requestedType in
	  add_node acc e (log_terminal+.l) context2) applications availableTerminals
  in ExpressionMap.map fst (enumerate (5,TypeMap.empty) rt bound)
;;



let test_enumerate () = 
  print_string (String.concat "\n" (List.map (fun (e,l) -> string_of_expression e) (ExpressionMap.bindings (enumerate_bounded polynomial_library (make_arrow tint tint) 15.0))));;

test_enumerate ();;
