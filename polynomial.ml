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

let encapsulatedEC (* a function that makes EC easier to use *)
    initial_primitives (* a list of combinations to be added to the library at the beginning *)
    tasks (* a list of tasks to be solved. see the file task.ml *)
    iterations (* how many iterations to run EC *)
    ?lambda:(lambda = 1.5) (* this parameter controls how eager the system is to add new things to the grammar. Increase if you see over fitting and decrease if you see under fitting of grammar structure. *)
    ?smoothing:(smoothing = 1.0) (* pseudo- counts for grammar parameter estimation. Increase if you see over fitting and decrease if you see under fitting of grammar parameters. *)
    ?frontier_size:(frontier_size = 10000) (* how many programs to enumerate in each iteration of EC *)
    ?log_prefix:(log_prefix = "grammar") (* grammars will be logged under log/LOGPREFIXlog_iteration *)
  =
  let g = ref (make_flat_library initial_primitives) in
  for i = 1 to iterations do 
    Printf.printf "\n \n \n Iteration %i \n" i;
    g := expectation_maximization_iteration ("log/"^log_prefix^string_of_int i)
        lambda smoothing frontier_size tasks (!g)
  done;
  List.map ~f:(fun (e,(l,_)) -> (e,l)) (snd !g)


let poly () = 
  let frontier_size = Int.of_string (Sys.argv.(1)) in
  let interval = 0--9 in
  let tasks = 
    List.concat (List.map ~f:(fun b ->
	(List.map ~f:(fun c -> make_polynomial_task 0 b c)
    interval)) interval) in
  encapsulatedEC
    [c_S;c_B;c_C;c_I;c_plus;c_times;c_zero;c_one;] (* primitives *)
    tasks
    8 (* iterations *)
    ~lambda:1.5 (* lambda *)
    ~smoothing:1.0 (* smoothing parameter *)
    ~frontier_size:frontier_size
    ~log_prefix:"polynomial_" (* log files will have this prefix *)
;;


poly ();;
