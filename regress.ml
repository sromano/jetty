open Em
open Task
open Expression
open Type
open Utils
open Library
open Ec
open Symbolic_dimensionality_reduction


let make_regression_task polynomial_coefficients sin_coefficients cos_coefficients = 
  let polynomial_string = String.concat " + " @@ List.mapi (fun power c -> 
      match (power,c) with
      | (0,_) -> string_of_int c
      | (1,1) -> "x"
      | (1,_) -> string_of_int c ^ "x"
      | (_,1) -> "x^" ^ string_of_int power
      | _ -> string_of_int c ^ "x^" ^ string_of_int power) polynomial_coefficients in
  let sin_string = String.concat " + " @@ List.mapi (fun w c -> 
      match (w+1,c) with
      | (1,1) -> "sin(x)"
      | (1,_) -> string_of_int c ^ "sin(x)"
      | (_,1) -> "sin(" ^ string_of_int (w+1) ^ ")"
      | _ -> string_of_int c ^  "sin(" ^ string_of_int (w+1) ^ ")") sin_coefficients in
  let cos_string = String.concat " + " @@ List.mapi (fun w c -> 
      match (w+1,c) with
      | (1,1) -> "cos(x)"
      | (1,_) -> string_of_int c ^ "cos(x)"
      | (_,1) -> "cos(" ^ string_of_int (w+1) ^ ")"
      | _ -> string_of_int c ^  "cos(" ^ string_of_int (w+1) ^ ")") cos_coefficients in
  let n = String.concat " + " [polynomial_string;sin_string;cos_string;] in
  let test_cases = 0--5 |> List.map float_of_int in
  let expression_test_cases = List.map expression_of_float test_cases in
  let correct_values = test_cases |> List.map (fun x -> 
      let p = List.mapi (fun power c -> float_of_int c *. (x ** (float_of_int power))) polynomial_coefficients in
      let p = List.fold_left (+.) 0. p in
      let s = sin_coefficients |> List.mapi (fun w c ->
          float_of_int c *. (sin (x *. (float_of_int w +. 1.)))) in
      let s = List.fold_left (+.) 0. s in
      let c = cos_coefficients |> List.mapi (fun w c ->
          float_of_int c *. (cos (x *. (float_of_int w +. 1.)))) in
      let c = List.fold_left (+.) 0. c in
      p +. s +. c) in
  let scoring_function = (fun (e : expression) -> 
      let rec t y c = 
        match y with
	  [] -> 0.0
        | (x::xs) -> 
	  let q = Application(e,x) in
	  match run_expression_for_interval 0.01 q with
	    Some(r) when r = List.hd c -> t xs (List.tl c)
	  | _ -> neg_infinity
      in t expression_test_cases correct_values)
  in { name = n; task_type = treal @> treal; 
       score = LogLikelihood(scoring_function); proposal = None; }


let regress () = 
  let g = ref fourier_library in
  let interval = 0--9 in
  let tasks = 
    List.concat (List.map (fun a ->
      List.concat (List.map (fun b ->
	(List.map (fun c -> make_regression_task [] [a;b;c] [])
	  interval)) interval)) interval) in
   for i = 1 to 8 do
    Printf.printf "\n \n \n Iteration %i \n" i;
    g := expectation_maximization_iteration ("log/iter_"^string_of_int i) 1.5 1.0 2000 tasks (!g)
  done;
(*  g := load_library "log/iter_1_grammar" ;
  let decoder =
    reduce_symbolically (polynomial_library) !g 100000 tasks in
  Printf.printf "Decoder: %s\n" (string_of_expression decoder) *)
;;


regress ();;
