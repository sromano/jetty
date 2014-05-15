open Expression
open Type
open Utils
open Library

module PQ = Set.Make
  (struct
     type t = float * int (* pair of priority (likelihood) and datum (program ID) *)
     let compare = compare
   end)

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

let match_template dagger template i = 
  let bindings = ref [] in
  let rec m t j = 
    match t with
    | Terminal("?",_,_) -> true
    | Terminal(name,_,_) when name.[0] = '?' -> begin
        let name_ID = int_of_string @@ String.sub name 1 (String.length name - 1) in
        try
          let k = List.assoc name_ID !bindings in
          match combine_wildcards dagger j k with
          | None -> false
          | Some(c) -> begin
            bindings := !bindings |> List.map (fun (i,l) -> 
                (i, if i = name_ID then c else l));
            true
          end
        with _ -> (bindings := (name_ID,j) :: !bindings; true)
      end
    | Application(f,x) -> begin
        try
          match extract_node dagger j with
          | ExpressionLeaf(_) -> false
          | ExpressionBranch(f_,x_) -> m f f_ && m x x_
        with _ -> raise (Failure "match_template, ID not in graph")
      end
    | Terminal(name,_,_) -> begin
        try
          match extract_node dagger j with
          | ExpressionLeaf(Terminal(name_,_,_)) -> name == name_
          | _ -> false
        with _ -> raise (Failure "match_template, ID not in graph")
      end
  in if m template i
     then Some(List.map snd @@ List.sort (fun (a,_) (b,_) -> compare a b) !bindings)
     else None
    
let apply_template template bindings = 
  let rec apply t = 
    match t with
    | Terminal(name,_,_) when name.[0] = '?' && String.length name > 1 -> begin
        let name_ID = int_of_string @@ String.sub name 1 (String.length name - 1) in
        try
          List.nth bindings name_ID
        with _ -> raise (Failure "apply_template: unbound")
      end
    | Terminal(_,_,_) -> t
    | Application(f,x) -> 
      Application(apply f,apply x)
  in apply template

let backward_children dagger grammar request rewrites j = 
  let (i2n,_,_) = dagger in
  let rec children i = 
    let head_rewrites = rewrites |> List.fold_left (fun a (template,handler) -> 
        match match_template dagger template i with
        | None -> a
        | Some(bindings) ->
          (handler @@ List.map (extract_expression dagger) bindings)::a) [] in
    match Hashtbl.find i2n i with
    | ExpressionLeaf(_) -> head_rewrites
    | ExpressionBranch(f,x) -> 
      let left = extract_expression dagger f in
      let right = extract_expression dagger x in
      let left_children = children f |> List.map (fun l -> 
          Application(l,right)) in
      let right_children = children x |> List.map (fun r -> 
          Application(left,r)) in
      head_rewrites @ left_children @ right_children
  in children j |> List.map (fun e -> (likelihood_option grammar request e, e)) |>
     List.filter (compose is_some fst) |> 
     List.map (fun (l,e) -> (insert_expression dagger e, get_some l))

let backward_enumerate dagger grammar rewrites size request i =
  let closed = ref @@ PQ.singleton (0.,i) in
  let opened = ref @@ PQ.singleton (0.,i) in
  let rec search () = 
    if PQ.cardinal !closed > size || PQ.cardinal !opened = 0
    then PQ.elements !closed
    else let next = PQ.max_elt !opened in
         opened := PQ.remove next !opened;
         backward_children dagger grammar request rewrites (snd next) |> 
         List.iter (fun (j,l) -> let c = (l,j) in
                   if PQ.mem c !closed then ()
                   else begin
                     closed := PQ.add c !closed;
                     opened := PQ.add c !opened
                   end);
         search ()
  in search ()

let i_rewrite = (expression_of_string "?0", fun e -> Application(c_I,List.hd e));;
let b_rewrite = (expression_of_string "(?0 (?1 ?2))",
                 apply_template (expression_of_string "(((B ?0) ?1) ?2)"));;
let c_rewrite = (expression_of_string "((?0 ?1) ?2)",
                 apply_template (expression_of_string "(((C ?0) ?2) ?1)"));;
let s_rewrite = (expression_of_string "((?0 ?2) (?1 ?2))",
                 apply_template (expression_of_string "(((S ?0) ?1) ?2)"));;
let k_rewrite = (expression_of_string "?0",
                 apply_template (expression_of_string "((K ?0) ?)"));;
let append_rewrite1 = (expression_of_string "?0",
                       apply_template @@ expression_of_string "((@ null) ?0)");;
let append_rewrite2 = (expression_of_string "((cons ?0) ((@ ?1) ?2))",
                      apply_template @@ expression_of_string "((@ ((cons ?0) ?1)) ?2)");;

let test_backwards () = 
  let dagger = make_expression_graph 1000 in
  let l = make_flat_library [c_S;c_B;c_C;c_I;c_K;c_append;c_cons;c_null;c_one;] in
  snd l |> ExpressionMap.bindings |> List.iter (fun (e,_) -> 
    ignore(insert_expression dagger e));
  let rewrites = 
    [i_rewrite; b_rewrite;c_rewrite;s_rewrite;append_rewrite1;append_rewrite2;k_rewrite;]
  in
  backward_enumerate dagger l rewrites 1000 t1
    (insert_expression dagger @@ expression_of_string "1") |> List.iter (fun (_,e) -> 
    Printf.printf "%s\n" @@ string_of_expression @@ extract_expression dagger e);;


test_backwards ();;
