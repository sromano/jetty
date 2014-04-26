
module IntMap = Map.Make(struct type t = int let compare = compare end)
module IntSet = Set.Make(struct type t = int let compare = compare end)

let compose f g = fun x -> f (g x);;


let is_invalid (x : float) = x <> x || x = infinity || x = neg_infinity;;
let is_valid = compose not is_invalid;;


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
  !b;;


let (--) i j = 
  let rec aux n acc =
    if n < i then acc else aux (n-1) (n :: acc)
  in aux j [] ;;
