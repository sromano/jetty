

module IntMap = Map.Make(struct type t = int let compare = compare end)

let is_invalid (x : float) = x <> x || x = infinity || x = neg_infinity;;

let lse x y = 
  if is_invalid x then y else if is_invalid y then x else
  if x > y
  then x +. log (1.0 +. exp (y-.x))
  else y +. log (1.0 +. exp (x-.y))
;;

let lse_list l = 
  List.fold_left lse neg_infinity l;;
