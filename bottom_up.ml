open Expression
open Type
open Utils
open Library
open Task
open Compress
open Partial_evaluation


module PQ = Set.Make
  (struct
     type t = float * int (* pair of priority (likelihood) and datum (program ID) *)
     let compare = compare
   end)

(* generation of bottom-up templates *)
let get_templates e t = 
  (* maximum number of times we can make up a value for a wildcard *)
  let maximum_barriers = 10 in
  (* uses partial evaluation to get templates *)
  let rec collect_templates barriers target template = 
    if barriers > maximum_barriers then [] else
    match reduce_expression template with
    | Stepped(new_template) -> 
      (target,new_template) :: collect_templates barriers target new_template
    | NormalForm -> []
    | Blocked(w,instantiations) -> 
      let new_targets = instantiations |> List.map (substitute_wildcard target w) in
      let new_templates = instantiations |> List.map (substitute_wildcard template w) in
      List.map2 (collect_templates @@ barriers+1) new_targets new_templates |> List.concat
  in
  let arity = get_arity t in
  0--arity |> List.map (fun number_arguments -> 
    let arguments = 1--number_arguments |> List.map (fun a -> make_wildcard @@ a+1) in
    let target = arguments |> List.fold_left (fun f x -> Application(f,x)) e in
    collect_templates 0 target target) 
  |> List.concat

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
                   if not (PQ.mem c !closed)
                   then begin
                     closed := PQ.add c !closed;
                     opened := PQ.add c !opened
                   end);
         search ()
  in search ()

let backward_iteration
    prefix lambda smoothing frontier_size rewrites
    tasks grammar = 
  let dagger = make_expression_graph 100000 in
  let frontiers = tasks |> List.map (fun t -> 
    Printf.printf "Enumerating (backwards) for %s..." t.name;
    print_newline ();
    let i = insert_expression dagger @@ match t.score with
      | Seed(s) -> s
      | LogLikelihood(_) -> raise (Failure "backward_iteration: task has no seed") in
    backward_enumerate dagger grammar rewrites frontier_size t.task_type i) in
  let type_array = infer_graph_types dagger in  
  let requests = List.fold_left2 (fun requests frontier t -> 
      let requested_type = t.task_type in
      List.fold_left (fun (a : (tp list) IntMap.t) (i : int) -> 
          try
	    let old = IntMap.find i a in
	    if List.mem requested_type old
	    then a else IntMap.add i (requested_type::old) a
          with Not_found -> IntMap.add i [requested_type] a
	) requests frontier
    ) IntMap.empty (List.map (List.map snd) frontiers) tasks
  in
  let task_solutions = List.combine tasks @@ 
    List.map (List.map (fun (_,i) -> (i,0.))) frontiers
  in
  let g = compress lambda smoothing dagger type_array requests task_solutions in
  (* save the grammar *)
  let c = open_out (prefix^"_grammar") in
  Printf.fprintf c "%s" (string_of_library g);
  close_out c;
  (* save the best programs *)
(*   let task_solutions = List.combine tasks program_scores |> List.map (fun (t,solutions) ->
    (t, solutions |> List.map (fun (i,s) -> 
          (i,s+. (get_some @@ likelihood_option g t.task_type (extract_expression dagger i)))))) in
  save_best_programs (prefix^"_programs") dagger task_solutions;
 *)  g

(* 
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
 *)


let test_templates () = 
  [c_I; c_K;c_C;c_S;c_B;c_append;c_last_one;] |> List.iter (fun c -> 
    get_templates c (infer_type c) |> List.iter (fun (target,template) -> 
        Printf.printf "%s ---> %s" (string_of_expression target) (string_of_expression template);
        print_newline ()));;


test_templates ();;

(* test_backwards ();; *)
