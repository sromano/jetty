
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


let hash_bindings h = 
  let b = ref [] in
  Hashtbl.iter (fun k v -> b := (k,v)::(!b)) h;
  !b


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
;;

let lse_list l = 
  List.fold_left lse neg_infinity l;;


let rec remove_duplicates l = 
  match l with
    [] -> []
  | (x::y) -> x::(List.filter (fun z -> not (z = x)) (remove_duplicates y));;


let combine_with f _ a b = 
  match (a,b) with
    (None,_) -> b
  | (_,None) -> a
  | (Some(x),Some(y)) -> Some(f x y);;


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
