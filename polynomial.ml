open Em
open Task
open Expression
open Type
open Utils
open Library
open Ec
open Symbolic_dimensionality_reduction


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
  in { name = n; task_type = make_arrow tint tint; 
       score = LogLikelihood(scoring_function); proposal = None; }

let super_task = 
  { name = "super"; task_type = make_arrow tint (make_arrow tint (make_arrow tint tint));
    proposal = None; score = LogLikelihood(fun e ->
    let test_cases = [(1,3,5);(0,2,2);(3,1,0);(2,1,3);(5,2,3);] in
    let rec t y =
      match y with
	[] -> 0.0
      | ((a,b,x)::xs) -> 
	let q = Application(Application(Application(e,expression_of_int b),
                                 expression_of_int a),expression_of_int x) in
	match run_expression_for_interval 0.01 q with
	  Some(r) when r = a*x+b -> t xs
	| _ -> neg_infinity
    in t test_cases     ); }


let poly () = 
  let g = ref (polynomial_library) in
  let interval = 0--9 in
  let tasks = 
    List.concat (List.map (fun a ->
      List.concat (List.map (fun b ->
	(List.map (fun c -> make_polynomial_task a b c)
	  interval)) interval)) interval)  in
(*   for i = 1 to 15 do
    Printf.printf "\n \n \n Iteration %i \n" i;
    let g1 = expectation_maximization_iteration ("log/iter_"^string_of_int i) 1.5 1.0 10000 tasks (!g) in
    g := g1
  done;
 *)  g := load_library "log/iter_15_grammar";
  let g1 = expectation_maximization_iteration ("log/super") 0.5 0.4 1000 [super_task] (!g) in 
  ()
(*   let decoder =
    reduce_symbolically (polynomial_library) !g 100000 tasks in
  Printf.printf "Decoder: %s\n" (string_of_expression decoder) *)
;;


poly ();;
