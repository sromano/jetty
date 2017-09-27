open Core.Std

open Em
open Task
open Expression
open Type
open Utils
open Library
open Ec
open Symbolic_dimensionality_reduction


let make_polynomial_task a b c =
  let n = Printf.sprintf "(%i x^2 + %i x + %i)^2" a b c in
  let test_cases : int list = 0--5 in
  let scoring_function = (fun (e : expression) ->
      let rec t y =
        match y with
	  [] -> 0.0
        | (x::xs) ->
	  let q = Application(e,Terminal(string_of_int x,TID(0),Obj.magic (ref x))) in
	  match run_expression_for_interval 0.01 q with
	    Some(r) when r = (a*x*x+b*x+c)*(a*x*x+b*x+c) -> t xs
	  | _ -> Float.neg_infinity
      in t test_cases)
  in { name = n; task_type = make_arrow tint tint;
       score = LogLikelihood(scoring_function); proposal = None; }


let poly () =
  let frontier_size = Int.of_string (Sys.argv.(1)) in
  let g = ref (polynomial_library) in
  let interval = 0--9 in
  let tasks =
    List.concat (List.map ~f:(fun b ->
	(List.map ~f:(fun c -> make_polynomial_task 0 b c)
           interval)) interval) in
  for i = 1 to 8 do
    Printf.printf "\n \n \n Iteration %i \n" i;
    g := expectation_maximization_iteration ("log/polynomial_"^string_of_int i)
        1.5 1.0 frontier_size tasks (!g)
  done;
  (*  g := load_library "log/iter_1_grammar" ;
      let decoder =
      reduce_symbolically (polynomial_library) !g 100000 tasks in
      Printf.printf "Decoder: %s\n" (string_of_expression decoder) *)
;;


poly ();;
