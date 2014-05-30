
module IntMap = Map.Make(struct type t = int let compare = compare end)
module IntSet = Set.Make(struct type t = int let compare = compare end)

let compose f g = fun x -> f (g x);;

let is_some = function
  | None -> false
  | _ -> true;;
let get_some = function
  | Some(x) -> x
  | _ -> raise (Failure "get_some");;
let safe_get_some message = function
  | Some(x) -> x
  | _ -> raise (Failure message);;

let memorize f sz = 
  let table = Hashtbl.create sz in
  fun x -> try
    Hashtbl.find table x
  with Not_found -> 
    let y = f x in
    Hashtbl.add table x y;
    y

let null = function
  | [] -> true
  | _ -> false

let rec take n = function
  | h::t when n > 0 -> h::(take (n-1) t)
  | _ -> []

let rec map_list f = function
  | [] -> [f []]
  | (x :: xs) -> (f (x :: xs)) :: (map_list f xs)

let hash_bindings h = 
  let b = ref [] in
  Hashtbl.iter (fun k v -> b := (k,v)::(!b)) h;
  !b

let rec list_equal c x y = 
  match (x,y) with
  | ([],_) -> null y
  | (_,[]) -> false
  | (a::b,p::q) -> c a p = 0 && list_equal c b q

let merge_a_list c ls = 
  let merged = Hashtbl.create 100000 in
  List.iter (fun l ->
    List.iter (fun (tag,value) -> 
      try
	let old_value = Hashtbl.find merged tag in
	Hashtbl.replace merged tag (c value old_value)
      with Not_found -> Hashtbl.add merged tag value
	      ) l
	    ) ls;
  hash_bindings merged

let is_invalid (x : float) = x <> x || x = infinity || x = neg_infinity;;
let is_valid = compose not is_invalid;;

let rec last_one = function
  | [] -> raise (Failure "last_one: empty")
  | [x] -> x
  | x::y -> last_one y

let index_of l x = 
  let rec loop a r = 
    match r with
      [] -> raise (Failure "index_of: not found")
    | (y::ys) -> if y = x then a else loop (a+1) ys
  in loop 0 l

let log2 = log 2.

let lse x y = 
  if is_invalid x then y else if is_invalid y then x else
  if x > y
  then x +. log (1.0 +. exp (y-.x))
  else y +. log (1.0 +. exp (x-.y))


let lse_list l = 
  List.fold_left lse neg_infinity l

(* log difference exponential: log(e^x - e^y) = x+log(1-e^(y-x)) *)
let lde x y = 
  assert(x >= y);
  x +. log (1. -. exp (y-.x))


let rec remove_duplicates l = 
  match l with
  | [] -> []
  | (x::y) -> x::(List.filter (fun z -> not (z = x)) (remove_duplicates y))


let combine_with f _ a b = 
  match (a,b) with
  | (None,_) -> b
  | (_,None) -> a
  | (Some(x),Some(y)) -> Some(f x y)


let hash_bindings h = 
  let b = ref [] in
  Hashtbl.iter (fun k v -> b := (k,v)::(!b)) h;
  !b


let (--) i j = 
  let rec aux n acc =
    if n < i then acc else aux (n-1) (n :: acc)
  in aux j []

let time_it description callback = 
  let start_time = Sys.time () in
  let return_value = callback () in
  Printf.printf "%s in %f seconds." description (Sys.time () -. start_time); print_newline ();
  return_value

(* progress bar *)
type progress_bar = { maximum_progress : int; mutable current_progress : int; }

let make_progress_bar number_jobs = 
  { maximum_progress = number_jobs; current_progress = 0; }

let update_progress_bar bar new_progress = 
  let max = float_of_int bar.maximum_progress in
  let old_dots = int_of_float @@ float_of_int bar.current_progress *. 80.0 /. max in
  let new_dots = int_of_float @@ float_of_int new_progress *. 80.0 /. max in
  bar.current_progress <- new_progress;
  if new_dots > old_dots then
    (1--(new_dots-old_dots)) |> List.iter (fun _ -> print_char '.'; flush stdout)

(* paralleled map *)
let pmap ?processes:(processes=4) ?bsize:(bsize=0) f input output =
  let bsize = match bsize with
    | 0 -> Array.length output / processes
    | x -> x
  in
  (* Given the starting index of a block, computes ending index *)
  let end_idx start_idx = min ((Array.length output) - 1) (start_idx+bsize-1) in
  let next_idx, total_computed = ref 0, ref 0
  and in_streams = ref []
  in
  while !total_computed < Array.length output do
    (* Spawn processes *)
    while !next_idx < Array.length output && List.length !in_streams < processes do
      let rd, wt = Unix.pipe () in
      match Unix.fork () with
      | 0 -> begin
	  (* Child *)
	  Unix.close rd;
	  let start_idx = !next_idx in
	  let answer    = Array.init (end_idx start_idx - start_idx + 1)
              (fun i -> f (input (i+start_idx))) in
	  let chan = Unix.out_channel_of_descr wt in
	  Marshal.to_channel chan (start_idx, answer) [Marshal.Closures];
	  close_out chan;
	  exit 0
	end
      | pid -> begin
	  (* Parent *)
	  Unix.close wt;
	  in_streams := (rd,pid)::!in_streams;
	  next_idx   := !next_idx + bsize;
	end
    done;
    (* Receive input from processes *)
    let recvs, _, _ = Unix.select (List.map fst !in_streams) [] [] (-1.) in
    List.iter (fun descr ->
        let chan = Unix.in_channel_of_descr descr in
        let pid = List.assoc descr !in_streams
        and start_idx, answer = Marshal.from_channel chan in
        ignore (Unix.waitpid [] pid);
        close_in chan;
        Array.blit answer 0 output start_idx (Array.length answer);
        total_computed := Array.length answer + !total_computed)
      recvs;
    in_streams := List.filter (fun (stream,_) -> not (List.mem stream recvs)) !in_streams;
  done;
  output


let number_of_cores = 4 (* number of CPUs *)
