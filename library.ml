open Expression
open Type


open Obj


module ExpressionMap = Map.Make(struct type t =expression let compare = compare_expression end)

type library = float * float ExpressionMap.t;;

(* creates a new library with all the production weights equal *)
let make_flat_library primitives = 
  (log 0.5, List.fold_left (fun a p -> ExpressionMap.add p 0.0 a)
  ExpressionMap.empty primitives);;



(* various built-in primitives *)
let c_S = Terminal("S", 
		  make_arrow (make_arrow t1 (make_arrow t2 t3))
		             (make_arrow (make_arrow t1 t2)
			                 (make_arrow t1 t3)),
		  Obj.magic (ref (fun f g x -> (f x) (g x))));;
let c_B = Terminal("B", 
		  make_arrow (make_arrow t2 t3)
		             (make_arrow (make_arrow t1 t2)
			                 (make_arrow t1 t3)),
		  Obj.magic (ref (fun f g x -> f (g x))));;
let c_C = Terminal("C", 
		  make_arrow (make_arrow t1 (make_arrow t2 t3))
		             (make_arrow t2 (make_arrow t1 t3)),
		  Obj.magic (ref (fun f g x -> (f x) g)));;
let c_K = Terminal("K",
		   make_arrow t1 (make_arrow t2 t1),
		   Obj.magic (ref (fun x _ -> x)));;
let c_I = Terminal("I",
		   make_arrow t1 t1,
		   Obj.magic (ref (fun x -> x)));;
let combinatory_library = 
  make_flat_library [c_S;c_B;c_C;c_K;c_I];;


let c_one = Terminal("1",make_ground "int",Obj.magic (ref 1));;
let c_zero = Terminal("0",make_ground "int",Obj.magic (ref 0));;
let c_plus = Terminal("+",
		     make_arrow (make_ground "int") (make_arrow (make_ground "int") (make_ground "int")),
		     Obj.magic (ref (fun x y ->x+y )));;
let c_times = Terminal("*",
		     make_arrow (make_ground "int") (make_arrow (make_ground "int") (make_ground "int")),
		     Obj.magic (ref (fun x y ->x*y )));;
let polynomial_library = 
  make_flat_library [c_S;c_B;c_C;c_K;c_I;c_one;c_zero;c_plus;c_times];;


let test_library () = 
  let i =make_app (make_app c_S c_K) c_K in
  let i2 =make_app (make_app c_B i) i in
  print_string (show_type (infer_type i2));;


 (* test_library ();; *)
