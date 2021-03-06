open Core.Std

open Em
open Task
open Expression
open Type
open Utils
open Library
open Ec
open Symbolic_dimensionality_reduction
open Noisy_reduction
open Type


let default_test_cases = List.map ((-5)--5) Float.of_int;;

let make_r2r ?test_cases:(test_cases=default_test_cases) std n f =
  let expression_test_cases = List.map ~f:expression_of_float test_cases in
  let correct_values = List.map test_cases ~f:(fun x ->
      normal std 0. +. f x) in
  let scoring_function = (fun (e : expression) -> 
      let rec t y c = 
        match y with
	| [] -> 0.0
        | (x::xs) -> 
	  let q = Application(e,x) in
	  match run_expression_for_interval 0.01 q with
	  | Some(r)  -> 
            let err = List.hd_exn c -. r in
            -. err*.err/.(2.*.std*.std) +. t xs (List.tl_exn c)
	  | _ -> Float.neg_infinity
      in t expression_test_cases correct_values)
  in { name = n; task_type = treal @> treal; 
       score = LogLikelihood(scoring_function); proposal = None; }


let make_regression_task std polynomial_coefficients sin_coefficients cos_coefficients = 
  let polynomial_string = String.concat ~sep:" + " @@ 
    List.mapi polynomial_coefficients (fun power c -> 
      match (power,c) with
      | (0,_) -> string_of_int c
      | (1,1) -> "x"
      | (1,_) -> string_of_int c ^ "x"
      | (_,1) -> "x^" ^ string_of_int power
      | _ -> string_of_int c ^ "x^" ^ string_of_int power) in
  let sin_string = String.concat ~sep:" + " @@ 
    List.mapi sin_coefficients (fun w c -> 
      match (w+1,c) with
      | (1,1) -> "sin(x)"
      | (1,_) -> string_of_int c ^ "sin(x)"
      | (_,1) -> "sin(" ^ string_of_int (w+1) ^ ")"
      | _ -> string_of_int c ^  "sin(" ^ string_of_int (w+1) ^ ")") in
  let cos_string = String.concat ~sep:" + " @@ 
    List.mapi cos_coefficients (fun w c -> 
      match (w+1,c) with
      | (1,1) -> "cos(x)"
      | (1,_) -> string_of_int c ^ "cos(x)"
      | (_,1) -> "cos(" ^ string_of_int (w+1) ^ ")"
      | _ -> string_of_int c ^  "cos(" ^ string_of_int (w+1) ^ ")") in
  let n = String.concat ~sep:" + " [polynomial_string;sin_string;cos_string;] in
  let f x =
      let p = List.mapi polynomial_coefficients (fun power c -> Float.of_int c *. (x ** (Float.of_int power))) in
      let p = List.fold_left p ~f:(+.) ~init:0. in
      let s = List.mapi sin_coefficients (fun w c ->
          Float.of_int c *. (sin (x *. (Float.of_int w +. 1.)))) in
      let s = List.fold_left s ~f:(+.) ~init:0. in
      let c = List.mapi cos_coefficients (fun w c ->
          Float.of_int c *. (cos (x *. (Float.of_int w +. 1.)))) in
      let c = List.fold_left c ~f:(+.) ~init:0. in
      p +. s +. c in
  make_r2r std n f


let higher_order () =
  let name = Sys.argv.(1) ^ Sys.argv.(2) in
  let inner = Sys.argv.(2).[0] = 'i' in
  let frontier_size = Int.of_string (Sys.argv.(3)) in
  let lambda = Float.of_string Sys.argv.(4) in
  let alpha = Float.of_string Sys.argv.(5) in
  let fs = [(sin,"sin");(cos,"cos");((fun x -> x*.x),"square")] in
  let inner_test_cases = float_interval (-1.0) 0.2 1.0 in
  let tasks = List.concat @@ List.map (0--9) ~f:(fun a ->
      let a = Float.of_int a in
      List.map fs ~f:(fun (f,n) ->
          if inner then
            make_r2r 0.25 (n ^ "(" ^ Float.to_string a ^ "x)") (fun x -> f (a*.x)) ~test_cases:inner_test_cases
          else
            make_r2r 1. (Float.to_string a ^ n ^ "(x)") (fun x -> a*. f (x)))) in
  let g = ref fourier_library in
  for i = 1 to 1 do
    Printf.printf "\n \n \n Iteration %i \n" i;
    g := expectation_maximization_iteration ("log/"^name^"_"^string_of_int i) lambda alpha frontier_size tasks (!g)
  done;
  let decoder =
    noisy_reduce_symbolically ~arity:2 fourier_library !g frontier_size tasks in
  Printf.printf "Decoder: %s\n" (string_of_expression decoder)
;;

let linear () =
  let name = Sys.argv.(1) ^ Sys.argv.(2) in
  let squared = Sys.argv.(2).[0] = 's' in
  let frontier_size = Int.of_string (Sys.argv.(3)) in
  let lambda = Float.of_string Sys.argv.(4) in
  let alpha = Float.of_string Sys.argv.(5) in
  let tasks = List.concat @@ List.map (0--9) ~f:(fun a ->
      let a = Float.of_int a in
      List.map (0--9) ~f:(fun b ->
          let b = Float.of_int b in
          if squared then
            make_r2r 2. ("(" ^ Float.to_string a ^ "x+"^Float.to_string b ^")^2") (fun x -> (a*.x+.b)*.(a*.x+.b))
          else
            make_r2r 1. ("(" ^ Float.to_string a ^ "x+"^Float.to_string b ^")") (fun x -> (a*.x+.b)))) in
  let g = ref fourier_library in
  for i = 1 to 5 do
    Printf.printf "\n \n \n Iteration %i \n" i;
    g := expectation_maximization_iteration ("log/"^name^"_"^string_of_int i) lambda alpha frontier_size tasks (!g)
  done;
  let decoder =
    noisy_reduce_symbolically ~arity:2 fourier_library !g frontier_size tasks in
  Printf.printf "Decoder: %s\n" (string_of_expression decoder)
;;


let regress () = 
  let name = Sys.argv.(1) in
  let lambda = Float.of_string Sys.argv.(3) in
  let alpha = Float.of_string Sys.argv.(4) in
  let g = ref fourier_library in
  let frontier_size = Int.of_string (Sys.argv.(2)) in
  let process_task a b c = 
    match Sys.argv.(1) with
    | "sin" -> make_regression_task 0.5 [] [a;b;c] []
    | "cos" -> make_regression_task 0.5 [] [] [a;b;c]
    | "quadratic" -> make_regression_task 0.5 [a;b;c] [] [] 
    | _ -> raise (Failure "process_task")
  in
  let interval = 0--9 in
  let tasks = 
    List.concat (List.map ~f:(fun a ->
      List.concat (List.map ~f:(fun b ->
	(List.map ~f:(fun c -> process_task a b c)
	  interval)) interval)) interval) in
   for i = 1 to 8 do
    Printf.printf "\n \n \n Iteration %i \n" i;
    g := expectation_maximization_iteration ("log/"^name^"_"^string_of_int i) lambda alpha frontier_size tasks (!g)
  done;
  let decoder =
    noisy_reduce_symbolically ~arity:2 fourier_library !g frontier_size tasks in
  Printf.printf "Decoder: %s\n" (string_of_expression decoder)
;;

let sanity_check g = 
  let g = load_library g in
  let t = t1 @> t2 @> treal @> treal in
  let ds = [(* "((+. ?b) ((*. ?a) ?x))"; "((B ((S *.) I)) ((+. ?b) ((*. ?a) ?x)))" *)
  "((*. ?a) (?b ?x))"] |> 
           List.map ~f:(remove_lambda "?x" % remove_lambda "?a" % remove_lambda "?b" % expression_of_string) in
  List.iter ds ~f:(fun d -> 
      print_endline         (string_of_expression d);
      Printf.printf "%s\n\t%f\n\t%f\n\n"
        (string_of_expression d)
        (get_some  @@ likelihood_option g t d)
        (get_some  @@ likelihood_option g (treal @> treal) @@  Application(Application(d,c_sin ),
                                                                  expression_of_float 5.)));;

(* sanity_check "grammars/hio";; *)

(* let list_check () = 
  let e = expression_of_string "((dot ((cons 1.) ((cons ?x) ((cons (sin ?x)) null)))) ?c)" |>
          remove_lambda "?x" |> remove_lambda "?c" in
  print_string @@ (string_of_expression e);
  print_newline ();
  print_string @@ string_of_type @@ infer_type e;
  let t = (TCon("list",[treal])) @> treal @> treal in
  Printf.printf "%f\n" (get_some @@ likelihood_option math_list_library t e);;

list_check ();;
 *)
let () = 
  match Sys.argv.(1) with
  | "hi" -> higher_order ()
  | "linear" -> linear ()
  | _ -> regress ()
;;


