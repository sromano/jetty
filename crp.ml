open Core.Std

open Expression
open Type
open Utils
open Library
open Task

type restaurant = (expression * tp * int ref) list

exception Restaurant_exception of (unit -> unit);;

let rec sample_restaurant_once alpha ?height:(height = 10) u r t = 
  if height < 1 then raise (Restaurant_exception u) else
  let matches = List.filter_map r ~f:(fun (e,et,n) ->
      match instantiated_type et t with
      | Some(it) -> Some(e,it,n)
      | None -> None) in
  let d = List.fold_left matches ~init:alpha ~f:(fun x (_,_,y) -> x +. Float.of_int !y) in
  let rec pick_match threshold = function
    | [] -> 
      let (f,ft,r,u) = sample_restaurant_once alpha ~height:(height - 1) u r (function_request t) in
      let (x,_,r,u) = sample_restaurant_once alpha ~height:(height - 1) u r (argument_request t ft) in
      let e = Application(f,x) in
      let et = infer_type e in (* type of (f x) *)
      let t = instantiated_type et t |> safe_get_some "sample_restaurant_once: could not instantiate (1)" in
      let r = (e,et,ref 1) :: r in
      (e,t,r,u)
    | (e,it,n)::ms -> 
      let e_threshold = (Float.of_int !n)/.d in
      if threshold > e_threshold
      then pick_match (threshold-.e_threshold) ms
      else begin
        incr n;
        (e,it,r,fun () -> decr n)
      end
  in pick_match (Random.float 1.0) matches

let rec sample_restaurant a r t = 
  try
    sample_restaurant_once a (fun () -> ()) r t
  with Restaurant_exception(u) -> 
    u ();
    sample_restaurant a r t
    

(* destructively modifies r *)
let rec restaurant_likelihood alpha r t e = 
  let matches = List.filter_map r ~f:(fun (e,et,n) ->
      match instantiated_type et t with
      | Some(it) -> Some(e,it,n)
      | None -> None) in
  let d = alpha +. List.fold_left matches ~init:0.0 ~f:(fun x (_,_,y) -> x +. Float.of_int !y) in
  let rec pick_match = function
    | [] -> 
      let (fl,ft,r) = restaurant_likelihood alpha r (function_request t) (application_function e) in
      let (xl,_,r) = restaurant_likelihood alpha r (argument_request t ft) (application_argument e) in
      let et = infer_type e in (* type of (f x) *)
      let t = instantiated_type et t |> safe_get_some "restaurant_likelihood: could not instantiate (1)" in
      let r = (e,et,ref 1) :: r in
      let l = log (alpha /. d)  +. fl +. xl in
      (l,t,r)
    | (q,et,n)::_ when compare_expression q e = 0 -> 
      begin
        let l = log (Float.of_int !n /. d) in
        incr n;
        (l,et,r)
      end
    | _::rest -> pick_match rest
  in pick_match matches

let make_restaurant primitives = 
  List.map primitives ~f:(fun p -> (p,infer_type p,ref 1))

let rec unseat_program restaurant e = 
  let rec walk_restaurant = function
    | [] -> raise (Failure "unseat_program: not in restaurant")
    | (q,_,n)::_ when 0 = compare_expression q e -> 
      if !n = 1
      then begin
        let restaurant = List.filter restaurant ~f:(fun (q,_,_) -> not (0 = compare_expression q e)) in
        match e with
        | Application(f,x) -> 
          let restaurant = unseat_program restaurant f in
          unseat_program restaurant x
        | _ -> raise (Failure "unseat_program: last terminal")
      end
      else begin
        decr n;
        restaurant
      end
    | _::r -> walk_restaurant r
  in walk_restaurant restaurant

let rec seat_program r p = 
  let rec find_it = function
    | [] -> 
      let r = (p,infer_type p,ref 1) :: r in
      begin
        match p with
        | Application(f,x) -> 
          seat_program (seat_program r f) x
        | _ -> raise (Failure "seat_program: terminal not in restaurant")
      end
    | (e,_,c)::_ when 0 = compare_expression e p -> begin
      incr c;
      r
    end
    | _::rest -> find_it rest
  in find_it r

(* Returns restaurant *)
let restaurant_Gibbs alpha ?tries:(tries = 10000) r task_array program_array = 
  let n = Random.int (Array.length task_array) in
  let r = match program_array.(n) with
  | Some(p) -> unseat_program r p
  | None -> r in
  let t = task_array.(n).task_type in
  let l = task_likelihood task_array.(n) in
  let rec replace = function
    | 0 -> begin
        match program_array.(n) with
        | Some(p) -> seat_program r p
        | None -> r end
    | k -> 
      let (p,_,rp,u) = sample_restaurant alpha r t in
      if is_valid (l p)
      then begin
        program_array.(n) <- Some(p);
        rp
      end else begin
        u ();
        replace (k - 1)
      end
  in
  replace tries

(* Returns map estimate, output string *)
let run_Gibbs ?silent:(silent = false) alpha basis tasks iterations = 
  let r = make_restaurant basis in
  let tasks = Array.of_list tasks in
  let posterior ps = 
    Array.foldi ps ~init:(0,0.0,make_restaurant basis) ~f:(fun i (cnt,l,r) p -> 
        match p with
        | None -> (cnt,l,r)
        | Some(p) -> 
          let (lp,_,r) = restaurant_likelihood alpha r (tasks.(i).task_type) p in
          (cnt + 1,l+.lp,r)) |> 
    (fun (a,b,_) -> (a,b))
  in 
  let rec find_best i r ps (best_posterior, best_frontiers) = 
    if i = 0 then (best_frontiers,snd best_posterior) else
      let r = restaurant_Gibbs alpha r tasks ps in
      let new_posterior = posterior ps in
      if new_posterior > best_posterior
      then find_best (i-1) r ps (new_posterior, Array.to_list ps)
      else find_best (i-1) r ps (best_posterior, best_frontiers)
  in
  let (best_frontier,best_posterior) = find_best iterations r (Array.map tasks ~f:(fun _ -> None)) 
      ((0,log 0.0),Array.to_list tasks |> List.map ~f:(fun _ -> None)) in
  let l1 = Printf.sprintf "Finished Gibbs sampling; best solution (%f) was:\n" best_posterior in
  let ls = List.map2_exn (Array.to_list tasks) best_frontier ~f:(fun t po -> 
    match po with
    | None -> Printf.sprintf "%s\tMissed\n" (t.name)
    | Some(p) -> Printf.sprintf "%s\t%s\n" (t.name) (string_of_expression p)) in
  let msg = l1 ^ String.concat ~sep:"" ls in
  (if not silent then print_string msg);
  (best_frontier,msg)

let run_parallel_Gibbs alpha basis tasks iterations = 
  let cs = cpu_count () in
  let seeds = List.map (1--cs) ~f:(fun _ -> Random.bits ()) in
  let ss = parallel_map seeds ~f:(fun seed ->
      Random.init seed;
      run_Gibbs ~silent:true alpha basis tasks iterations) in
  List.iter ss ~f:(fun (_,m) -> 
    Printf.printf "\n%s\n\n" m)
      

(* 
let () = 
  let r () = make_restaurant [(*c_S;c_B;c_C;*)c_I;(*c_plus;*)c_times; (*c_zero; *)c_one;] in
  Random.init 2;
  let (_,es) = List.fold_left (0--4) ~init:(r (),[])
      ~f:(fun (rest,acc) _ ->
          let (e,_,rest,_) = sample_restaurant 2.0 rest (tint @> tint) in
          (rest,e::acc)) in
  List.iter es ~f:(fun e -> Printf.printf "%s\n" (string_of_expression e));
  let likelihood expressions = 
    List.fold_left expressions ~init:(r (),0.0)
      ~f:(fun (rest,acc) e -> 
          let (l,_,rest) = restaurant_likelihood 2.0 rest (tint @> tint) e in
          (rest,l+.acc)) in
  let es =  [expression_of_string "(* 1)"; expression_of_string "I"] in
  Printf.printf "%f\n" (snd @@ likelihood es);
  Printf.printf "%f\n" (snd @@ likelihood @@ List.rev es)
;;
 *)
