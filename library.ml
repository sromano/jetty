open Task
open Expression
open Type
open Utils

open Obj


(* specializes the list typed to only work on phonemes *)
let phonetic_list = true

type library = float * (float*tp) ExpressionMap.t

(* creates a new library with all the production weights equal *)
let make_flat_library primitives = 
  (log 0.35, List.fold_left (fun a p -> ExpressionMap.add p (0.0,infer_type p) a)
  ExpressionMap.empty primitives)

(* computes likelihoods of all expressions using a dynamic program *)
(* program_types is a hashmap from ID to type
   requests maps from ID to list of all requested types *)
(* returns a hash map from (ID,requested type) to log likelihood *)
let program_likelihoods (log_application,library) dagger program_types requests = 
  let log_terminal = log (1.0 -. exp log_application) in
  (* store map from production ID to log probability *)
  let terminals = ExpressionMap.bindings library |> List.map (fun (e,(l,_)) ->
      (insert_expression dagger e, l)) in 
  (* get all of the different types we can choose from *)
  let terminal_types =
    List.map (fun (_,(l,t)) -> (t,l)) (ExpressionMap.bindings library) in
  let likelihoods = Hashtbl.create (expression_graph_size dagger) in
  let rec likelihood (i : int) (request : tp) = 
    if is_wildcard dagger i then 0. else
    try
      Hashtbl.find likelihoods (i,request)
    with Not_found -> 
      let log_probability = 
        let terminal_probability = 
          let numerator = terminals |> List.fold_left (fun a (j,l) -> 
            if can_match_wildcards dagger i j then lse a l else a) neg_infinity in
          if is_invalid numerator
          then neg_infinity
          else let z = lse_list (List.map snd (List.filter (fun (t,_) -> 
              can_unify t request) terminal_types)) in
            numerator+.log_terminal-.z
        in match extract_node dagger i with
          ExpressionBranch(f,x) -> 
            let left_request = function_request request in
            let right_request = argument_request request program_types.(f) in
            let application_probability = log_application+. likelihood f left_request 
                                          +. likelihood x right_request in
            lse terminal_probability application_probability
        | _ -> terminal_probability
      in
      Hashtbl.add likelihoods (i,request) log_probability;
      log_probability
  in IntMap.iter (fun i -> List.iter (fun r -> ignore (likelihood i r))) requests; likelihoods

(* computes likelihood of a possibly ill typed program: returns None if it doesn't type *)
let likelihood_option library request e = 
  let dagger = make_expression_graph 100 in
  let i = insert_expression dagger e in
  let requests = IntMap.singleton i [request] in
  try
    let types = infer_graph_types dagger in
    let likelihoods = program_likelihoods library dagger types requests in
    Some(Hashtbl.find likelihoods (i,request))
  with _ -> None        

(* tracks the number of times that each production has been used, or could have been used *)
type useCounts = { 
    mutable application_counts : float; mutable terminal_counts : float;
    use_counts : float array; possible_counts : float array;
  }

(* uses the inside out algorithm to fit the continuous parameters of a grammar
   does so using a dynamic program similar to the one used to compute likelihoods
   smoothing specifies the number of pseudo-counts
   dagger is the expression graph
   program_types is a map from graph ID to type
   likelihood specifies the likelihood of each expression for each requested type
   corpus is a list of ((expression ID,requested type),weight)
   returns the grammar with the parameters fit *)
let fit_grammar smoothing (log_application,library) dagger program_types likelihoods corpus = 
  let log_terminal = log (1.0 -. exp log_application) in
  (* get all of the different terminals we can choose from;
     this ordering determines where they go in the use arrays
     "offsets" index into this list
   *)
  let terminal_order =
    List.mapi (fun i (e,(l,t)) -> (insert_expression dagger e,
                                   (t, l, i)))
      (ExpressionMap.bindings library) in
  let number_terminals = List.length terminal_order in
  let counts = { application_counts = log smoothing;
                 terminal_counts = log smoothing;
                 use_counts = Array.make number_terminals (log smoothing);
                 possible_counts = Array.make number_terminals (log smoothing); } in
  let rec uses weight i request = 
    if not (is_wildcard dagger i) then begin
      let l = Hashtbl.find likelihoods (i,request) in
      (* if it is in library compute uses if the production was used *)
      let hits = terminal_order |> List.filter
                   (fun (j,_) -> can_match_wildcards dagger i j) in
      if not (null hits) then begin
        let offsets = hits |> List.map (fun (_,(_,l,o)) -> (o,l)) in
        let offset_Z = lse_list @@ List.map snd offsets in
        let offsets = offsets |> List.map (fun (o,l) -> (o,l-.offset_Z)) in
        let others = List.filter (fun (_,(t,_,_)) -> can_unify t request) terminal_order in
        let other_offsets = List.map (fun (_,(_,_,o)) -> o) others in
        let z = lse_list (List.map (fun (_,(_,l,_)) -> l) others) in
        let terminal_likelihood = log_terminal+.offset_Z-.z -.l in
        offsets |> List.iter (fun (o,l) -> let u = counts.use_counts.(o) in
                               counts.use_counts.(o) <- lse u (l+.terminal_likelihood+.weight));
        other_offsets |> List.iter (fun o -> let p = counts.possible_counts.(o) in
                               counts.possible_counts.(o) <- lse p (terminal_likelihood+.weight));
        counts.terminal_counts <- lse counts.terminal_counts (terminal_likelihood+.weight)
      end;
      match extract_node dagger i with
      (* we have no children, don't recurse *)
      | ExpressionLeaf(_) -> ()
      (* recurse on function and argument *)
      | ExpressionBranch(f,x) ->
        (* get probability that an application was used *)
        let left_request = function_request request in
        let right_request = argument_request request program_types.(f) in
        let left_probability = if is_wildcard dagger f 
          then 0.
          else Hashtbl.find likelihoods (f,left_request) in
        let right_probability = if is_wildcard dagger x 
          then 0.
          else Hashtbl.find likelihoods (x,right_request) in
        let application_likelihood =
          log_application+.left_probability+.right_probability -.l in
        counts.application_counts <- 
          lse counts.application_counts (application_likelihood+.weight);
        (* get the uses from the right and the left *)
        uses (weight+.application_likelihood) f left_request;
        uses (weight+.application_likelihood) x right_request
    end
  in 
  List.iter (fun ((i,request),w) -> uses w i request) corpus;
  let log_application = counts.application_counts -. counts.terminal_counts in
  let distribution = List.fold_left (fun a (i,(_,_,o)) -> 
                                    let p = counts.use_counts.(o) -. counts.possible_counts.(o)
                                    and e = extract_expression dagger i
                                    in ExpressionMap.add e (p,infer_type e) a)
      ExpressionMap.empty terminal_order
  in (log_application,distribution)

(* wrapper over fit_grammar that does not assume a corpus structure *)
let fit_grammar_to_tasks smoothing grammar dagger program_types requests task_solutions = 
  let likelihoods = program_likelihoods grammar dagger program_types requests in
  let task_posteriors = task_solutions |> List.map (fun (t,s) ->
    s |> List.map (fun (i,l) -> 
          ((i,t.task_type),l+.Hashtbl.find likelihoods (i,t.task_type)))) in
  let zs = task_posteriors |> List.map (fun p -> 
    lse_list @@ List.map snd p) in
  let task_posteriors = List.map2 (fun p z -> 
    p |> List.map (fun (i,l) -> (i,l-.z))) task_posteriors zs in
  let corpus = merge_a_list lse task_posteriors in
  fit_grammar smoothing grammar dagger program_types likelihoods corpus

(* various built-in primitives *)
let c_S = Terminal("S", canonical_type @@  
                  make_arrow (make_arrow t1 (make_arrow t2 t3))
                             (make_arrow (make_arrow t1 t2)
                                         (make_arrow t1 t3)),
                  Obj.magic (ref (fun f -> 
                       Some(fun g -> 
                         Some(fun x ->
                             match f with
                             | None -> None
                             | Some(f) -> 
                               match f x with
                               | None -> None
                               | Some(left) -> 
                                 left @@ match g with
                                 | None -> None
                                 | Some(g) -> g x)))));;
let c_B = Terminal("B", canonical_type @@ 
                  make_arrow (make_arrow t2 t3)
                             (make_arrow (make_arrow t1 t2)
                                         (make_arrow t1 t3)),
                  Obj.magic (ref (fun f  -> 
                       Some(fun g -> 
                           Some(fun x -> 
                             match f with
                             | None -> None
                             | Some(f) -> 
                               f @@ match g with
                               | None -> None
                               | Some(g) -> g x)))));;
let c_C = Terminal("C",  canonical_type @@ 
                  make_arrow (make_arrow t1 (make_arrow t2 t3))
                             (make_arrow t2 (make_arrow t1 t3)),
                  Obj.magic (ref (fun f -> 
                       Some(fun g -> 
                         Some(fun x ->
                             match f with
                             | None -> None
                             | Some(f) -> 
                               match f x with
                               | None -> None
                               | Some(left) -> 
                                 left g)))));;
let c_K = Terminal("K", canonical_type @@ 
                   make_arrow t1 (make_arrow t2 t1),
                   Obj.magic (ref (fun x -> Some(fun _ -> x))));;
let c_I = Terminal("I", canonical_type @@ 
                   make_arrow t1 t1,
                   Obj.magic (ref (fun x -> x)));;
let combinatory_library = 
  make_flat_library [c_S;c_B;c_C;c_K;c_I]

let c_bottom = Terminal("bottom",canonical_type t1,Obj.magic @@ ref None)

let c_one = Terminal("1",tint,Obj.magic (ref 1));;
let c_zero = Terminal("0",tint,Obj.magic (ref 0));;
let c_numbers = 0--9 |> List.map expression_of_int;;
let c_plus = Terminal("+",
                     make_arrow tint (make_arrow tint tint),
                     lift_binary (+));;
let c_times = Terminal("*",
                     make_arrow tint (make_arrow tint tint),
                     lift_binary (fun x y ->x*y ));;
let polynomial_library = 
  make_flat_library @@ [c_S;c_B;c_C;c_I;c_plus;c_times;c_zero;c_one;](*  @ c_numbers *);;

let c_reals = 0--9 |> List.map (compose expression_of_float float_of_int);;
let c_sin = Terminal("sin",
                    make_arrow treal treal,
                    lift_unary sin);;
let c_cos = Terminal("cos",
                    make_arrow treal treal,
                    lift_unary cos);;
let c_plus_dot = Terminal("+.",
                     make_arrow treal (make_arrow treal treal),
                     lift_binary (+.));;
let c_times_dot = Terminal("*.",
                     make_arrow treal (make_arrow treal treal),
                     lift_binary ( *. ));;
let fourier_library = 
  make_flat_library @@ [c_S;c_B;c_C;c_I;c_plus_dot;c_times_dot;c_sin;c_cos;] @ c_reals;;


let list_type = if phonetic_list then make_ground "phone" else t1;;
let c_null = Terminal("null",canonical_type (TCon("list",[list_type])),Obj.magic (ref []));;
let c_cons = Terminal("cons",
                      canonical_type @@ make_arrow list_type @@ 
                      make_arrow (TCon("list",[list_type])) @@ (TCon("list",[list_type])),
                      lift_binary (fun x y -> x::y));;
let c_append = Terminal("@",
                        canonical_type @@ make_arrow (TCon("list",[list_type])) @@ 
                        make_arrow (TCon("list",[list_type])) @@ (TCon("list",[list_type])),
                        lift_binary (@));;
let c_last_one = Terminal("last-one",
                          canonical_type @@ make_arrow (TCon("list",[list_type])) list_type,
                          lift_unary last_one);;


let string_of_library (log_application,distribution) = 
  let bindings = ExpressionMap.bindings distribution in
  String.concat "\n"
    ((string_of_float (exp log_application))::
     (List.map (fun (e,(w,t)) -> Printf.sprintf "\t %f \t %s : %s " w (string_of_expression e) (string_of_type t)) 
        bindings));;

let all_terminals = ref ([c_K;c_S;c_B;c_C;c_I;c_bottom;
                          c_sin;c_cos;c_times_dot;c_plus_dot;c_plus;c_times;
                          c_null;c_append;c_cons;c_last_one] @ c_numbers @ c_reals |> 
                         List.map (fun e -> (string_of_expression e,e)));;
let register_terminal t = 
  all_terminals := (string_of_expression t,t) :: !all_terminals;;
let register_terminals = List.iter register_terminal;;

(* replaces all of the "unit references" with actual unit references. necessary for marshaling *)
let scrub_graph (i2n,n2i,_) = 
  let substitution = ref [] in
  Hashtbl.iter (fun i n -> 
    match n with
    | ExpressionLeaf(Terminal(name,t,r)) -> 
      let clean = ExpressionLeaf(Terminal(name,t,ref ()))
      and dirty = n in
      substitution := (i,clean,dirty) :: !substitution
    | _ -> ()) i2n;
  !substitution |> List.iter (fun (i,c,d) -> 
    Hashtbl.replace i2n i c;
    Hashtbl.remove n2i d;
    Hashtbl.add n2i c i)

(* undoes the above operation *)
let dirty_graph (i2n,n2i,_) =
  let substitution = ref [] in
  Hashtbl.iter (fun i n -> 
    match n with
    | ExpressionLeaf(Terminal(name,t,r)) -> 
      let clean = n
      and dirty = ExpressionLeaf(List.assoc name !all_terminals) in
      substitution := (i,clean,dirty) :: !substitution
    | _ -> ()) i2n;
  !substitution |> List.iter (fun (i,c,d) -> 
    Hashtbl.replace i2n i d;
    Hashtbl.remove n2i c;
    Hashtbl.add n2i d i)
  

(* parses an expression. has to be in library because needs definitions of terminals *)
let expression_of_string s = 
  let i = ref 0 in
  let rec read () = 
    if !i < String.length s
    then (if s.[!i] == '('
          then (incr i;
                let f = read () in
                incr i;
                let x = read () in
                incr i;
                Application(f, x))
          else (let j = ref (!i) in
                while !j < String.length s && s.[!j] <> ')' && s.[!j] <> ' ' do
                  incr j
                done;
                let name = String.sub s !i (!j - !i) in
                i := !j;
                if name.[0] = '?'
                then Terminal(name,t1,ref ())
                else try
                  List.assoc name !all_terminals
                with Not_found -> raise (Failure ("not in all_terminals: "^name))))
    else raise (Failure ("expression_of_string: "^s))
  in read ()

let load_library f = 
  let i = open_in f in
  let log_application = float_of_string @@ input_line i in
  let productions = ref [] in
  try
    while true do
      let l = String.trim @@ input_line i in
      let weight_index = String.index l ' ' in
      let w = float_of_string @@ String.sub l 0 weight_index in
      let e = expression_of_string @@ String.trim @@ 
        String.sub l weight_index (String.length l - weight_index) in
      productions := (e,w) :: !productions
    done; (0.,ExpressionMap.empty)
  with End_of_file -> 
    (log log_application, !productions |> 
    List.fold_left (fun a (e,w) -> ExpressionMap.add e (w,infer_type e) a) ExpressionMap.empty)



let test_library () = 
  ["I";"((C +) 1)";"(K (+ (0 S)))"] |> List.map 
    (fun s -> print_string (string_of_expression @@ expression_of_string s); print_newline ());;


(* test_library ();; *)
