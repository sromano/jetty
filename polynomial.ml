open Em
open Task
open Expression
open Type
open Utils
open Library



let make_polynomial_task a b c = 
  let n = Printf.sprintf "%i x^2 + %i x + %i" a b c in
  let test_cases : int list = 0--9 in
  let scoring_function = (fun (e : expression) -> 
    let rec t y = 
      match y with
	[] -> 0.0
      | (x::xs) -> 
	  let q = Application(e,Terminal(string_of_int x,TID(0),Obj.magic (ref x))) in
	  match run_expression_for_interval 0.01 q with
	    Some(r) when r = a*x*x+b*x+c -> t xs
	  | _ -> neg_infinity
    in t test_cases)
  in { name = n; task_type = make_arrow tint tint; score = scoring_function; }
;;


let poly () = 
  let g = ref (polynomial_library) in
  let interval = 0--9 in
  let tasks = 
    List.concat (List.map (fun a ->
      List.concat (List.map (fun b ->
	(List.map (fun c -> make_polynomial_task a b c)
	  interval)) interval)) interval)  in
  for i = 1 to 15 do
    Printf.printf "\n \n \n Iteration %i \n" i;
    let g1 = expectation_maximization_iteration 1.5 1.0 10000 tasks (!g) in
    g := g1
  done
;;

poly ();;
