open Core.Std

open Type
open Utils
open Drawing
open Em
open Task
open Expression
open Library
open Ec
open Symbolic_dimensionality_reduction


let make_drawing_task n expected =
  let scoring_function = (fun (e : expression) ->
    let empty = expression_of_draw (empty_drawing ()) in
    let q = Application(e,empty) in
    match run_expression_for_interval 0.01 q with
    Some(Draw(arr,_,_,_)) ->
      log (ssim_with_window arr expected 4) *. 1000.0
    | _ -> Float.neg_infinity) in
  {
    name = n;
    task_type = make_arrow tdraw tdraw;
    score = LogLikelihood(scoring_function);
    proposal = None;
  }

let make_drawing_task_with_init n expected x y =
  let scoring_function = (fun (e : expression) ->
    (*let cdraw = change_position (empty_drawing ()) x y in*)
    let cdraw = (empty_drawing ()) in
    let drawe = expression_of_draw cdraw in
    let xe = expression_of_int x in
    let ye = expression_of_int y in
    let q = Application(Application(Application(e,xe),ye),drawe) in
    match run_expression_for_interval 0.01 q with
    Some(Draw(arr,_,_,_)) when arr = expected -> 0.0
    | _ -> Float.neg_infinity) in
  {
    name = n;
    task_type = make_arrow tint (make_arrow tint (make_arrow tdraw tdraw));
    score = LogLikelihood(scoring_function);
    proposal = None;
  }

let get_line_task length =
  let line = move_drawing length (empty_drawing ()) in
  let expected = drawing_array line in
  let scoring_function = (fun (e : expression) ->
    let empty = expression_of_draw (empty_drawing ()) in
    let q = Application(e,empty) in
    match run_expression_for_interval 0.01 q with
    Some(Draw(arr,_,_,_)) ->
      (*let () = print_float (log (ssim_with_window arr expected 4)) in
      let () = print_newline() in
      let () = print_m arr in
      let () = print_newline() in
      let () = print_newline() in*)

      (* Here we might use some annealing *)
      log (ssim_with_window arr expected 8) *. 1000.0
    | _ -> Float.neg_infinity) in
  {
    name = "Line";
    task_type = make_arrow tdraw tdraw;
    score = LogLikelihood(scoring_function);
    proposal = None;
  }

let draw () =
  let frontier_size = Int.of_string (Sys.argv.(1)) in
  let g = ref (drawing_library) in
  let dim = 10 in
  let all_tasks =
    List.fold ~f:(fun acum i -> List.append acum (Csv.load Sys.argv.(i)))
      ~init:[] (2--(Array.length Sys.argv - 1)) in
  (*let names = List.hd_exn (Csv.load "graphic_tasks_names.txt") in*)
  let drawing_tasks = List.map ~f:( fun l -> split (List.map ~f:Float.of_string l) dim) all_tasks in
  let tasks = List.map ~f:(fun i ->
    let y = find_elem_row 1.0 i in
    let x = find_elem_pos 1.0 (List.nth_exn i y) in
    let arr = Array.of_list @@ List.map ~f:(Array.of_list) i in
    make_drawing_task_with_init "Square" arr x y) drawing_tasks in

  for i = 1 to 8 do
    Printf.printf "\n \n \n Iteration %i \n" i;
    g := expectation_maximization_iteration ("log/graphics_"^string_of_int i)
        1.5 1.0 frontier_size tasks (!g)
  done;
  (*  g := load_library "log/iter_1_grammar" ;
      let decoder =
      reduce_symbolically (polynomial_library) !g 100000 tasks in
      Printf.printf "Decoder: %s\n" (string_of_expression decoder) *)
;;


(*

print_drawing (move_one_step_drawing (move_one_step_drawing (rotate 2 (move_one_step_drawing (move_one_step_drawing (rotate 2 (move_one_step_drawing (move_one_step_drawing (rotate 2 (move_one_step_drawing (move_one_step_drawing (empty_drawing()))))))))))));;
print_drawing (move_one_step_drawing (move_one_step_drawing (rotate 2 (move_one_step (move_one_step (rotate 2 (move_one_step_drawing (move_one_step_drawing (rotate 2 (move_one_step (move_one_step (empty_drawing()))))))))))));;
print_drawing (move_drawing 4 (rotate 2 (move_drawing 4 (rotate 2 (move_drawing 4 (rotate 2 (move_drawing 4 (empty_drawing()))))))))

*)


let test_drawing () =

  let e1 = expression_of_draw (empty_drawing ()) in
  let one_step = Terminal("M1", make_arrow tdraw tdraw, lift_unary (move_one_step_drawing)) in
  let rotate = Terminal("R2", make_arrow tdraw tdraw, lift_unary (rotate 2)) in
  let x_steps = Terminal("MX", make_arrow tint (make_arrow tdraw tdraw), lift_binary (move_drawing)) in
  let x = expression_of_int 4 in

  let q = Application(one_step,e1) in

  let rotate = Application(rotate,q) in
  let move = Application(Application(x_steps,x),rotate) in

  let () = print_string (string_of_expression move) in
  let () = print_newline () in
  (match run_expression_for_interval 0.1 move with
    Some(x) -> print_drawing x;
    | None -> print_string "timeout"
  );;

let test_repeat () =

  let e1 = expression_of_draw (empty_drawing ()) in

  let repeat n base f =
    List.fold ~init:base ~f:(fun acum i -> f acum) (0--(n-1)) in

  let x = expression_of_int 4 in
  let y = expression_of_int 2 in
  let operation draw = Application(Application(d_rotate,y),Application(Application(d_drawing,x),draw)) in

  let q = repeat 4 e1 operation in

  let () = print_string (string_of_expression q) in
  let () = print_newline () in
  (match run_expression_for_interval 0.1 q with
    Some(x) -> print_drawing x;
    | None -> print_string "timeout"
);;

draw ();;
