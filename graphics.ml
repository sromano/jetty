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
DRAWING

matrix of points + current point + orientation

orientation:
0 1 2
7 x 3
6 5 4

*)

type drawtype =
  | Draw of float array array * int * int * int
  | OutOfBounds

let empty_matrix w h = Array.make_matrix w h 0.0

(* let empty_drawing w h = Draw(empty_matrix w h,0,0,0) *)
let empty_drawing () = Draw(empty_matrix 10 10,0,0,3)

let width draw =
  match draw with
  | Draw(arr,_,_,_) -> (Array.length arr)
  | OutOfBounds -> 0

let height draw =
  match draw with
  | Draw(arr,_,_,_) -> (Array.length arr.(0))
  | OutOfBounds -> 0

let update_position x y r =
  match r with
    | 0 -> (x-1,y-1)
    | 1 -> (x,y-1)
    | 2 -> (x+1,y-1)
    | 7 -> (x-1,y)
    | 3 -> (x+1,y)
    | 6 -> (x-1,y+1)
    | 5 -> (x,y+1)
    | 4 -> (x+1,y+1)
    | _ -> (-1,-1)

let rotate grad draw =
  match draw with
    | OutOfBounds -> OutOfBounds
    | Draw(arr,x,y,r) -> Draw(arr,x,y, (r + grad) mod 8)

let move_one_step draw =
  match draw with
    | OutOfBounds -> OutOfBounds
    | Draw(_,0,_,r) when List.mem [0;7;6] r -> OutOfBounds
    | Draw(_,_,0,r) when List.mem [0;1;2] r -> OutOfBounds
    | Draw(_,x,_,r) when x = (width draw) - 1 && List.mem [2;3;4] r -> OutOfBounds
    | Draw(_,_,y,r) when y = (height draw) - 1 && List.mem [6;5;4] r -> OutOfBounds
    | Draw(arr,x,y,r) ->
      let x2,y2 = update_position x y r in
      Draw(arr,x2,y2,r)

let move_one_step_drawing draw =
  match draw with
  | OutOfBounds -> OutOfBounds
  | Draw(arr,x,y,r) ->
    let () = arr.(y).(x) <- 1.0 in
    move_one_step draw

let rec move pen_down steps draw =
  if steps <= 0
    then draw
  else
    match draw with
    | OutOfBounds -> OutOfBounds
    | _ -> move pen_down (steps-1) (if pen_down then move_one_step_drawing draw else move_one_step draw)

let move_drawing = move true

let move_not_drawing = move false

let print_drawing draw =
  match draw with
  | Draw(arr,_,_,_) -> print_m arr
  | OutOfBounds -> print_string "Out of Bounds"

let ssim arrx arry =
  let ux = mean_a arrx in
  let uy = mean_a arry in
  let vx = variance_a arrx in
  let vy = variance_a arry in
  let cov = covariance_a arrx arry in
  let c1 = 0.0001 in
  let c2 = 0.0009 in
    (2.0 *. ux *. uy +. c1) *. (2.0 *. cov +. c2) /.
    ((ux *. ux +. uy *. uy +. c1) *. (vx +. vy +. c2))

(* images need to be square and equal size *)
let ssim_with_window arrx arry wsize =
  let n = (Array.length arrx) in
  let interval = 0--(n-wsize) in
  let results = List.concat (List.map (interval) ~f:(fun xi ->
    List.map (interval) ~f:(fun yi ->
      let startx = xi in
      let stopx = xi + wsize in
      let warrxx = List.map (yi--(yi+wsize-1)) ~f:(fun y -> Array.slice arrx.(y) startx stopx) in
      let warryy = List.map (yi--(yi+wsize-1)) ~f:(fun y -> Array.slice arry.(y) startx stopx) in
      let warrx = List.fold ~init:(Array.empty()) ~f:Array.append warrxx in
      let warry = List.fold ~init:(Array.empty()) ~f:Array.append warryy in
  ssim warrx warry))) in
  mean_a (Array.of_list results)

(* Should I add fixed point combinator? Repeat? Symmetry? *)

let d_rotate = Terminal("@", make_arrow tint (make_arrow tdraw tdraw), lift_binary (rotate));;

let d_drawing = Terminal("D", make_arrow tint (make_arrow tdraw tdraw), lift_binary (move_drawing));;

let d_ndrawing = Terminal("N", make_arrow tint (make_arrow tdraw tdraw), lift_binary (move_not_drawing));;

let drawing_library =
  make_flat_library @@ [c_S;c_B;c_C;c_I;d_rotate;d_drawing;d_ndrawing;]  @ c_numbers ;;


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

test_repeat ();;
