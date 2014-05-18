open Type
open Utils

open Unix
open Obj

type expression = 
  | Terminal of string * tp * unit ref
  | Application of expression * expression

let rec compare_expression e1 e2 = 
  match (e1,e2) with
    (Terminal(n1,_,_),Terminal(n2,_,_)) -> compare n1 n2
  | (Terminal(_,_,_),_) -> -1
  | (_,Terminal(_,_,_)) -> 1
  | (Application(l,r),Application(l_,r_)) -> 
      let c = compare_expression l l_ in
      if c == 0 then compare_expression r r_ else c


module ExpressionMap = Map.Make(struct type t =expression let compare = compare_expression end)
module ExpressionSet = Set.Make(struct type t =expression let compare = compare_expression end)


let terminal_type e = 
  match e with
  | Terminal(_,t,_) -> t
  | _ -> raise (Failure "terminal_type: not a terminal")

let terminal_thing e = 
  match e with
  | Terminal(_,_,t) -> t
  | _ -> raise (Failure "terminal_thing: not a terminal")

let rec run_expression (e:expression) : 'a = 
  match e with
    Terminal(_,_,thing) -> !(Obj.magic thing)
  | Application(f,x) -> 
      (Obj.magic (run_expression f)) (Obj.magic (run_expression x))

exception Timeout;;
let sigalrm_handler = Sys.Signal_handle (fun _ -> raise Timeout) ;;
let run_expression_for_interval (time : float) (e : expression) : 'a option = 
  let old_behavior = Sys.signal Sys.sigalrm sigalrm_handler in
   let reset_sigalrm () = Sys.set_signal Sys.sigalrm old_behavior 
   in ignore (Unix.setitimer ITIMER_REAL {it_interval = 0.0; it_value = time}) ;
      try
	let res = run_expression e in 
	ignore (Unix.setitimer ITIMER_REAL {it_interval = 0.0; it_value = 0.0}) ;
	reset_sigalrm () ; Some(res)  
      with exc -> begin
        reset_sigalrm ();
 	ignore (Unix.setitimer ITIMER_REAL {it_interval = 0.0; it_value = 0.0}) ; 
        None
      end


let infer_type (e : expression) = 
  let rec infer c r = 
    match r with
      Terminal(_,t,_) -> instantiate_type c t
    | Application(f,x) -> 
	let (ft,c1) = infer c f in
	let (xt,c2) = infer c1 x in
	let (rt,c3) = makeTID c2 in
	let c4 = unify c3 ft (make_arrow xt rt) in
	chaseType c4 rt
  in fst (infer (1,TypeMap.empty) e)


let rec string_of_expression e = 
  match e with
    Terminal(s,_,_) -> s
  | Application(f,x) -> 
      "("^(string_of_expression f)^" "^(string_of_expression x)^")"


(* compact representation of expressions sharing many subtrees *)
type expressionNode = ExpressionLeaf of expression
  | ExpressionBranch of int * int;;
type expressionGraph = 
    ((int,expressionNode) Hashtbl.t) * ((expressionNode,int) Hashtbl.t) * (int ref);;
let make_expression_graph size : expressionGraph = 
  (Hashtbl.create size,Hashtbl.create size,ref 0)


let insert_expression_node (i2n,n2i,nxt) (n : expressionNode) : int =
  try
    Hashtbl.find n2i n
  with Not_found -> 
    Hashtbl.add i2n (!nxt) n;
    Hashtbl.add n2i n (!nxt);
    incr nxt; !nxt - 1;;


let rec insert_expression g (e : expression) = 
  match e with
    Terminal(_,_,_) ->
      insert_expression_node g (ExpressionLeaf(e))
  | Application(f,x) -> 
      insert_expression_node g (ExpressionBranch(insert_expression g f,insert_expression g x));;


let rec extract_expression g i = 
  let (i2n,_,_) = g in
  match Hashtbl.find i2n i with
    ExpressionLeaf(e) -> e
  | ExpressionBranch(f,x) -> 
      Application(extract_expression g f, extract_expression g x)

let extract_node (i2n,_,_) i = 
  try
    Hashtbl.find i2n i
  with Not_found -> raise (Failure "extract_node: ID not in graph")
    
let expression_graph_size (_,_,s) = !s

let is_leaf_ID (g,_,_) i = 
  match Hashtbl.find g i with
    ExpressionLeaf(_) -> true
  | _ -> false
  
let rec get_sub_IDs g i = 
  let (i2n,_,_) = g in
  match Hashtbl.find i2n i with
    ExpressionLeaf(_) -> IntSet.singleton i
  | ExpressionBranch(f,x) -> 
      IntSet.add i (IntSet.union (get_sub_IDs g f) (get_sub_IDs g x))

let is_wildcard dagger i = 
  match extract_node dagger i with
  | ExpressionLeaf(Terminal(n,_,_)) when n.[0] = '?' -> true
  | _ -> false

let rec has_wildcards dagger i = 
  match extract_node dagger i with
  | ExpressionBranch(f,x) -> has_wildcards dagger f || has_wildcards dagger x
  | ExpressionLeaf(Terminal("?",_,_)) -> true
  | _ -> false

let terminal_wildcard = function
  | Terminal(n,_,_) when n.[0] = '?' -> true
  | _ -> false

(* checks to see if the target could be matched to the template *)
let rec can_match_wildcards dagger template target = 
  if template = target then true else 
  match extract_node dagger template with
  | ExpressionLeaf(Terminal(n,_,_)) when n.[0] = '?' -> true
  | ExpressionLeaf(_) -> false
  | ExpressionBranch(template_function,template_argument) -> begin
    match extract_node dagger target with
    | ExpressionBranch(target_function,target_argument) -> 
      can_match_wildcards dagger template_function target_function && 
      can_match_wildcards dagger template_argument target_argument
    | _ -> false
  end

let rec combine_wildcards dagger i j = 
  if i = j then Some(j) else
  match extract_node dagger i with
  | ExpressionLeaf(Terminal("?",_,_)) -> Some(j)
  | ExpressionLeaf(Terminal(n,_,_)) -> (
    match extract_node dagger j with
    | ExpressionLeaf(Terminal("?",_,_)) -> Some(i)
    | _ -> None)
  | ExpressionBranch(l,r) -> (
    match extract_node dagger j with
    | ExpressionBranch(m,n) -> (
        match combine_wildcards dagger m l with
        | None -> None
        | Some(a) -> (
          match combine_wildcards dagger r n with
          | None -> None
          | Some(b) -> Some(insert_expression_node dagger (ExpressionBranch(a,b)))))
    | ExpressionLeaf(Terminal("?",_,_)) -> Some(i)
    | _ -> None)
  | ExpressionLeaf(_) -> raise (Failure "leaf not terminal in wildcards")

let make_wildcard w = 
  Terminal("?" ^ string_of_int w,t1, ref ())

let rec maximum_wildcard = function
  | Application(f,x) -> max (maximum_wildcard f) (maximum_wildcard x)
  | Terminal(n,_,_) when n.[0] = '?' -> int_of_string @@ String.sub n 1 @@ String.length n - 1
  | _ -> -1

let rec map_wildcard f = function
  | Application(m,n) -> Application(map_wildcard f m,map_wildcard f n)
  | Terminal(n,_,_) when n.[0] = '?' -> 
    f @@ int_of_string @@ String.sub n 1 @@ String.length n - 1
  | e -> e

let substitute_wildcard original w new_W = 
  let offset = maximum_wildcard original in
  let new_W = map_wildcard (fun w -> make_wildcard @@ w+offset) new_W in
  map_wildcard (fun q -> if q = w then new_W else make_wildcard q) original


(* performs type inference upon the entire graph of expressions *)
(* returns an array whose ith element is the type of the ith expression *)
let infer_graph_types dagger = 
  let type_map = Array.make (expression_graph_size dagger) (TID(0)) in
  let done_map = Array.make (expression_graph_size dagger) false in
  let (i2n,_,_) = dagger in
  let rec infer i = 
    if done_map.(i) then type_map.(i)
    else let q = (match Hashtbl.find i2n i with
      ExpressionLeaf(Terminal(_,t,_)) -> t
    | ExpressionBranch(f,x) -> 
	let ft = infer f in
	let xt = infer x in
	application_type ft xt
    | _ -> raise (Failure "leaf that is not a terminal")) in
    done_map.(i) <- true; type_map.(i) <- q; q
  in for i = 0 to (expression_graph_size dagger - 1) do
    ignore (infer i)
  done; type_map

let test_expression () =
  let t1 = TID(0) in
  let e1 = Terminal("I", t1, Obj.magic (ref (fun x -> x))) in
  let e42 = Terminal("31", t1, Obj.magic (ref 31)) in
  let e2 = Terminal("1", t1, Obj.magic (ref 1)) in
  let e3 = Application(Application(e1,e1),e2) in
  let e4 = Terminal("+", t1, Obj.magic (ref (fun x -> fun y -> x+y))) in
  let e5 = Application(Application(e4,e3),e42) in
  let p = Terminal("p",t1,Obj.magic (ref (fun x -> Thread.delay 0.05; x))) in
  let q = Application(p,e5) in
  (match run_expression_for_interval 0.01 q with
    Some(x) -> print_int x
  | None -> print_string "timeout");
  (match run_expression_for_interval 0.1 q with
    Some(x) -> print_int x
  | None -> print_string "timeout");
  Thread.delay 1.;
  (match run_expression_for_interval 0.1 q with
    Some(x) -> print_int x
  | None -> print_string "timeout")
;;


 (* test_expression ();;  *)
