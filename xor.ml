open Core.Std

open Em
open Task
open Expression
open Type
open Utils
open Library
open Ec
open Symbolic_dimensionality_reduction

(*

EXPERIMENT

p
p xor q
p xor q xor r
r xor s
p and (q xor r)
p and (q or r)

p
p or q
p and q
r or s
p and (q xor r)
p and (q or r)

*)

(* UTILITY FUNCTIONS *)
let test_cases = [[0;0;0;0];[0;0;0;1];[0;0;1;0];[0;0;1;1];[0;1;0;0];[0;1;0;1];[0;1;1;0];[0;1;1;1];[1;0;0;0];[1;0;0;1];[1;0;1;0];[1;0;1;1];[1;1;0;0];[1;1;0;1];[1;1;1;0];[1;1;1;1]];;

let apply_forth x e =
    let terminal = (fun i -> Terminal(string_of_int i, TID(i), Obj.magic (ref i))) in
    let p = Application(e, (terminal (List.nth_exn x 0))) in
    let q = Application(p, (terminal (List.nth_exn x 1))) in
    let r = Application(q, (terminal (List.nth_exn x 2))) in
    Application(r, (terminal (List.nth_exn x 3)));;
let t4 =
  let t = make_arrow tint tint in
  let t2 = make_arrow tint t in
  let t3 = make_arrow tint t2 in
  make_arrow tint t3;;


(* XOR GROUP TASKS *)
let make_xor_task_x1 =
  let n = "p" in
  let scoring_function = (fun (e : expression) ->
      let rec t y =
        match y with
    [] -> 0.0
        | (x::xs) ->
    let s = apply_forth x e in
    match run_expression_for_interval 0.01 s with
      Some(r) when r = (List.nth_exn x 0) -> t xs
    | _ -> Float.neg_infinity
      in t test_cases)
  in { name = n; task_type = t4;
       score = LogLikelihood(scoring_function); proposal = None; }

let make_xor_task_x2 =
  let n = "p xor q" in
  let scoring_function = (fun (e : expression) ->
      let rec t y =
        match y with
    [] -> 0.0
        | (x::xs) ->
    let s = apply_forth x e in
    match run_expression_for_interval 0.01 s with
      Some(r) when r = (List.nth_exn x 0) lxor (List.nth_exn x 1) -> t xs
    | _ -> Float.neg_infinity
      in t test_cases)
  in { name = n; task_type = t4;
       score = LogLikelihood(scoring_function); proposal = None; }

let make_xor_task_x3 =
  let n = "p xor q xor r" in
  let scoring_function = (fun (e : expression) ->
      let rec t y =
        match y with
    [] -> 0.0
        | (x::xs) ->
    let s = apply_forth x e in
    match run_expression_for_interval 0.01 s with
      Some(r) when r = (List.nth_exn x 0) lxor (List.nth_exn x 1) lxor (List.nth_exn x 2) -> t xs
    | _ -> Float.neg_infinity
      in t test_cases)
  in { name = n; task_type = t4;
       score = LogLikelihood(scoring_function); proposal = None; }

let make_xor_task_x4 =
  let n = "r xor s" in
  let scoring_function = (fun (e : expression) ->
      let rec t y =
        match y with
    [] -> 0.0
        | (x::xs) ->
    let s = apply_forth x e in
    match run_expression_for_interval 0.01 s with
      Some(r) when r = (List.nth_exn x 2) lxor (List.nth_exn x 3) -> t xs
    | _ -> Float.neg_infinity
      in t test_cases)
  in { name = n; task_type = t4;
       score = LogLikelihood(scoring_function); proposal = None; }

(* CONTROL GROUP TASKS *)
let make_xor_task_c1 = make_xor_task_x1;;
let make_xor_task_c2 =
  let n = "p or q" in
  let scoring_function = (fun (e : expression) ->
      let rec t y =
        match y with
    [] -> 0.0
        | (x::xs) ->
    let s = apply_forth x e in
    match run_expression_for_interval 0.01 s with
      Some(r) when r = (List.nth_exn x 0) lor (List.nth_exn x 1) -> t xs
    | _ -> Float.neg_infinity
      in t test_cases)
  in { name = n; task_type = t4;
       score = LogLikelihood(scoring_function); proposal = None; }
let make_xor_task_c3 =
  let n = "p and q" in
  let scoring_function = (fun (e : expression) ->
      let rec t y =
        match y with
    [] -> 0.0
        | (x::xs) ->
    let s = apply_forth x e in
    match run_expression_for_interval 0.01 s with
      Some(r) when r = (List.nth_exn x 0) land (List.nth_exn x 1) -> t xs
    | _ -> Float.neg_infinity
      in t test_cases)
  in { name = n; task_type = t4;
       score = LogLikelihood(scoring_function); proposal = None; }
let make_xor_task_c4 =
  let n = "r or s" in
  let scoring_function = (fun (e : expression) ->
      let rec t y =
        match y with
    [] -> 0.0
        | (x::xs) ->
    let s = apply_forth x e in
    match run_expression_for_interval 0.01 s with
      Some(r) when r = (List.nth_exn x 2) lor (List.nth_exn x 3) -> t xs
    | _ -> Float.neg_infinity
      in t test_cases)
  in { name = n; task_type = t4;
       score = LogLikelihood(scoring_function); proposal = None; }

(* TEST TASKS *)
let make_xor_task_t1 =
  let n = "p and (q xor r)" in
  let scoring_function = (fun (e : expression) ->
      let rec t y =
        match y with
    [] -> 0.0
        | (x::xs) ->
    let s = apply_forth x e in
    match run_expression_for_interval 0.01 s with
      Some(r) when r = (List.nth_exn x 0) land ( (List.nth_exn x 1) lxor (List.nth_exn x 2)) -> t xs
    | _ -> Float.neg_infinity
      in t test_cases)
  in { name = n; task_type = t4;
       score = LogLikelihood(scoring_function); proposal = None; }

let make_xor_task_t2 =
  let n = "p and (q or r)" in
  let scoring_function = (fun (e : expression) ->
      let rec t y =
        match y with
    [] -> 0.0
        | (x::xs) ->
    let s = apply_forth x e in
    match run_expression_for_interval 0.01 s with
      Some(r) when r = (List.nth_exn x 0) land ( (List.nth_exn x 1) lor (List.nth_exn x 2)) -> t xs
    | _ -> Float.neg_infinity
      in t test_cases)
  in { name = n; task_type = t4;
       score = LogLikelihood(scoring_function); proposal = None; }


let xor () =
  let frontier_size = Int.of_string (Sys.argv.(1)) in
  let g = ref (boolean_library_with_xor) in (* boolean_library *)
  let tasks = [make_xor_task_x1;make_xor_task_x2;make_xor_task_x3;make_xor_task_x4] in
  for i = 1 to 8 do
    Printf.printf "\n \n \n Iteration %i \n" i;
    g := expectation_maximization_iteration ("log/xor_"^string_of_int i)
        1.5 1.0 frontier_size tasks (!g)
  done;
  let test_tasks = [make_xor_task_t1;make_xor_task_t2;] in
  for i = 1 to 16 do
    Printf.printf "\n \n \n Test Iteration %i \n" i;
    g := expectation_maximization_iteration ("log/xor_"^string_of_int i)
        1.5 1.0 frontier_size (List.append tasks test_tasks) (!g)
  done;

  (*  g := load_library "log/iter_1_grammar" ;
      let decoder =
      reduce_symbolically (polynomial_library) !g 100000 tasks in
      Printf.printf "Decoder: %s\n" (string_of_expression decoder) *)
;;

(* TESTING CODE BEFORE RUN *)

let test_xor_task () =

    let lift_quaternary k : unit ref = Obj.magic @@ ref (
        fun x -> Some(fun y -> Some(fun z -> Some (fun w ->
                    match (x,y,z,w) with
                        | (Some(a),Some(b),Some(c),Some(d)) -> Some(k a b c d)
                                | _ -> None)))) in

    let e = Terminal("fst", make_arrow tint (make_arrow tint tint), (lift_quaternary @@ fun a b c d -> a)) in
    let task = make_xor_task_x1 in
    let ll = match task.score with
        | Seed(_) -> raise (Failure "score_programs: task has seed")
                | LogLikelihood(ll) -> ll in
    let l = ll e in

    print_float l;
    print_newline();

    let terminal = (fun i -> Terminal(string_of_int i, TID(i), Obj.magic (ref i))) in
    let p = Application(e, (terminal 0 )) in
    let q = Application(p, (terminal 1 )) in
    let r = Application(q, (terminal 0 )) in
    let s = Application(r, (terminal 0 )) in
    (match run_expression_for_interval 0.01 s with
        Some(r) -> print_int r
            | _ -> print_string "pum");
    print_newline();
;;

let test_xor_task2 () =

    let e = Terminal("xor", make_arrow tint (make_arrow tint tint), (lift_quaternary @@ fun a b c d -> a lxor b)) in
    let task = make_xor_task_x2 in
    let ll = match task.score with
        | Seed(_) -> raise (Failure "score_programs: task has seed")
                | LogLikelihood(ll) -> ll in
    let l = ll e in

    print_float l;
    print_newline();

    let terminal = (fun i -> Terminal(string_of_int i, TID(i), Obj.magic (ref i))) in
    let p = Application(e, (terminal 0 )) in
    let q = Application(p, (terminal 1 )) in
    let r = Application(q, (terminal 0 )) in
    let s = Application(r, (terminal 0 )) in
    (match run_expression_for_interval 0.01 s with
        Some(r) -> print_int r
            | _ -> print_string "pum");
    print_newline();
;;

(*
test_xor_task ();;
test_xor_task2 ();;
*)

xor();;
