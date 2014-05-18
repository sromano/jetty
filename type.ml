
module TypeMap = Map.Make(struct type t = int let compare = compare end)



type tp = 
    TID of int
  | TCon of string * tp list

type tContext = int * tp TypeMap.t
let empty_context = (0,TypeMap.empty);;
let make_arrow t q = TCon("->", [t;q]);;


let rec string_of_type t = 
  match t with
    TID(i) -> string_of_int i
  | TCon(k,[]) -> k
  | TCon(k,[p;q]) when k = "->" -> "("^(string_of_type p)^" -> "^(string_of_type q)^")"
  | TCon(k,a) -> "("^k^" "^(String.concat " " (List.map string_of_type a))^")"


let makeTID context = 
    (TID(fst context), (fst context+1, snd context))

let bindTID i t context = 
  (fst context, TypeMap.add i t (snd context))

let rec chaseType (context : tContext) (t : tp) : tp*tContext = 
    match t with
      TCon(s, ts) ->
	let (ts_, context_) = List.fold_right
	    (fun t (tz, k) ->
	      let (t_, k_) = chaseType k t in
	      (t_ :: tz, k_)) ts ([], context)
	in (TCon(s, ts_), context_)
    | TID(i) -> 
	try
	  let (t_, context_) = chaseType context (TypeMap.find i (snd context)) in
	  let substitution = TypeMap.add i t_ (snd context_) in
	  (t_, (fst context_, substitution))
        with Not_found -> (t,context)

let rec occurs (i : int) (t : tp) : bool = 
  match t with
    TID(j) -> j == i
  | TCon(_,ts) -> 
      List.exists (occurs i) ts

let occursCheck = true

let rec unify context t1 t2 : tContext = 
  let (t1_, context_) = chaseType context t1 in
  let (t2_, context__) = chaseType context_ t2 in
  unify_ context__ t1_ t2_
and unify_ context t1 t2 : tContext = 
  match (t1, t2) with
    (TID(i), TID(j)) when i == j -> context
  | (TID(i), _) ->
      if occursCheck && occurs i t2
      then raise (Failure "occurs")
      else bindTID i t2 context
  | (_,TID(i)) ->
      if occursCheck && occurs i t1
      then raise (Failure "occurs")
      else bindTID i t1 context
  | (TCon(k1,as1),TCon(k2,as2)) when k1 = k2 -> 
      List.fold_left2 (fun c a1 a2 -> unify c a1 a2) context as1 as2
  | _ -> raise (Failure "unify");;


type fast_type = 
    FCon of string * fast_type list
  | FID of (fast_type option) ref

let can_unify (t1 : tp) (t2 : tp) : bool =
  let rec same_structure t1 t2 =
    match (t1, t2) with
      (TCon(k1,as1), TCon(k2,as2)) when k1 = k2 -> 
	List.for_all2 same_structure as1 as2
    | (TID(_),_) -> true
    | (_,TID(_)) -> true
    | _ -> false
  in if not (same_structure t1 t2) then false else
  let rec make_fast_type dictionary t = 
    match t with
      TID(i) -> 
	(try List.assoc i !dictionary
	 with Not_found -> let f = FID(ref None) in dictionary := (i,f)::!dictionary; f)
    | TCon(k,xs) -> 
	FCon(k, List.map (make_fast_type dictionary) xs)
  in let rec fast_occurs r f = 
    match f with
      FID(r_) -> r == r_
    | FCon(_,fs) -> List.exists (fast_occurs r) fs
  in let rec fast_chase f = 
    match f with
      FID(r) ->
	(match !r with
	  None -> f
	| Some(f_) ->
	    let f__ = fast_chase f_ in
	    r := Some(f__); f__)
    | FCon(k,fs) -> FCon(k,List.map fast_chase fs)
  in let rec fast_unify t1 t2 = 
    match (t1,t2) with
      (FID(i1),FID(i2)) when i1 == i2 -> true
    | (FID(i),_) when fast_occurs i t2 -> false
    | (FID(i),_) -> i := Some(t2); true
    | (_,FID(i)) when fast_occurs i t1 -> false
    | (_,FID(i)) -> i := Some(t1); true
    | (FCon(k1,_),FCon(k2,_)) when k1 <> k2 -> false
    | (FCon(k1,[]),FCon(k2,[])) -> true
    | (FCon(k1,x::xs),FCon(k2,y::ys)) -> 
	fast_unify x y && List.for_all2 (fun a b -> fast_unify (fast_chase a) (fast_chase b)) xs ys
    | _ -> raise (Failure "constructors of different arity")
  in fast_unify (make_fast_type (ref []) t1) (make_fast_type (ref []) t2)
;;

let instantiate_type (n,m) t = 
  let substitution = ref [] in
  let next = ref n in
  let rec instantiate j = 
    match j with
      TID(i) -> (try TID(List.assoc i (!substitution))
		with Not_found -> substitution := (i,!next)::!substitution; next := (1+ !next); TID(!next-1)
		)
    | TCon(k,js) -> TCon(k,List.map instantiate js)
  in let q = instantiate t in
  (q,(!next,m))


(* puts a type into normal form *)
let canonical_type t = 
  let next = ref 0 in
  let substitution = ref [] in
  let rec canon q = 
    match q with
      TID(i) -> (try TID(List.assoc i (!substitution))
		with Not_found -> substitution := (i,!next)::!substitution; next := (1+ !next); TID(!next-1))
    | TCon(k,a) -> TCon(k,List.map canon a)
  in canon t

let rec next_type_variable t = 
  match t with
    TID(i) -> i+1
  | TCon(_,[]) -> 0
  | TCon(_,is) -> List.fold_left max 0 (List.map next_type_variable is)


let application_type f x = 
  let (f,c1) = instantiate_type empty_context f in
  let (x,c2) = instantiate_type c1 x in
  let (r,c3) = makeTID c2 in
  let c4 = unify c3 f (make_arrow x r) in
  canonical_type (fst (chaseType c4 r))

let argument_request request left = 
  let (request,c1) = instantiate_type empty_context request in
  let (left,c2) = instantiate_type c1 left in
  match left with
    TCon(_,[right;result]) -> 
      let c3 = unify c2 request result in
      canonical_type (fst (chaseType c3 right))
  | _ -> raise (Failure ("invalid function type: "^(string_of_type left)))

let function_request request = 
  canonical_type (make_arrow (TID(next_type_variable request)) request)

let rec get_arity = function
  | TCon(a,[_;r]) when a = "->" -> 1+get_arity r
  | _ -> 0


let make_ground g = TCon(g,[]);;
let tint = make_ground "int";;
let t1 = TID(1);;
let t2 = TID(2);;
let t3 = TID(3);;
let t4 = TID(4);;


let test_type () = 
  print_string (string_of_bool (can_unify (make_arrow t1 t1) (make_arrow t1 t1)));
  print_string (string_of_bool (can_unify (make_arrow t1 t1) (make_arrow (make_arrow t1 t2) t3)));
  print_string (string_of_bool (not (can_unify (make_arrow t1 t1) (make_arrow (make_arrow t1 t2) (make_ground "int")))));
;;
 (* test_type ();; *)
