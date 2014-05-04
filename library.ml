open Task
open Expression
open Type
open Utils

open Obj


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
  let terminals = Hashtbl.create 100 in
  ExpressionMap.bindings library |> List.iter (fun (e,(l,_)) ->
      Hashtbl.add terminals (insert_expression dagger e) l);
  (* get all of the different types we can choose from *)
  let terminal_types =
    List.map (fun (_,(l,t)) -> (t,l)) (ExpressionMap.bindings library) in
  let (i2n,n2i,nxt) = dagger in
  let likelihoods = Hashtbl.create (expression_graph_size dagger) in
  let rec likelihood (i : int) (request : tp) = 
    try
      Hashtbl.find likelihoods (i,request)
    with Not_found -> 
      let log_probability = 
        let terminal_probability = 
          try
            let my_likelihood = Hashtbl.find terminals i in
            let z = lse_list (List.map snd (List.filter (fun (t,_) -> 
                can_unify t request) terminal_types)) in
            log_terminal+.my_likelihood-.z
          with Not_found -> neg_infinity
        in match Hashtbl.find i2n i with
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
let likelihood_option (log_application,library) request e = 
  let log_terminal = log (1.0 -. exp log_application) in
  (* get all of the different types we can choose from *)
  let terminal_types =
    List.map (fun (_,(l,t)) -> (t,l)) (ExpressionMap.bindings library) in
  let rec l q r = 
    match q with
    | Terminal(_,t,_) -> 
      let log_probability = fst @@ ExpressionMap.find q library in
      let z = lse_list @@ List.map snd @@ 
        List.filter (compose (can_unify r) fst) terminal_types in
      (log_terminal+.log_probability-.z, t)
    | Application(f,x) -> 
      let (left_likelihood,f_type) = l f (function_request r) in
      let (right_likelihood,x_type) = l x (argument_request r f_type) in
      let application_likelihood = log_application+.left_likelihood+.right_likelihood in
      try
        let (log_probability,t) = ExpressionMap.find q library in
        let z = lse_list @@ List.map snd @@ 
          List.filter (compose (can_unify r) fst) terminal_types in
        (lse (log_terminal+.log_probability-.z) application_likelihood, t)
      with Not_found -> (application_likelihood, application_type f_type x_type)
  in try
    Some(fst @@ l e request)
  with _ -> None
    
        

(* tracks the number of times that each production has been used, or could have been used *)
type useCounts = { 
    application_counts : float; terminal_counts : float;
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
  let (i2n,n2i,nxt) = dagger in
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
  (* hash map from (ID,requested type) to use counts *)
  let use_map = Hashtbl.create (Hashtbl.length likelihoods) in
  let rec uses i request = 
    try
      Hashtbl.find use_map (i,request)
    with Not_found -> 
      let u = 
        (* if it is in library compute uses if the production was used *)
        let (terminal_probability,offset,distractors) =
          try
            (* this will fail if it is not in the library *)
            let (_,production_weight,offset) = List.assoc i terminal_order in
            let others = List.filter (fun (_,(t,_,_)) -> can_unify t request) terminal_order in
            let other_offsets = List.map (fun (_,(_,_,o)) -> o) others in
            let z = lse_list (List.map (fun (_,(_,l,_)) -> l) others) in
            (log_terminal+.production_weight-.z, offset, other_offsets) 
          with Not_found -> (neg_infinity, 0, [])
        in match Hashtbl.find i2n i with
          (* we have no children, don't recurse *)
          ExpressionLeaf(_) -> 
            { application_counts = 0.0; terminal_counts = 1.0;
              use_counts = Array.init number_terminals (fun j -> if j=offset then 1.0 else 0.0);
              possible_counts = Array.init number_terminals
                (fun j -> if List.mem j distractors then 1.0 else 0.0); }
          (* recurse on function and argument *)
        | ExpressionBranch(f,x) ->
            (* get probability that an application was used *)
            let left_request = function_request request in
            let right_request = argument_request request program_types.(f) in
            let left_probability = Hashtbl.find likelihoods (f,left_request) in
            let right_probability = Hashtbl.find likelihoods (x,right_request) in
            let application_probability = log_application+.left_probability+.right_probability in
            (* get the uses from the right and the left *)
            let left_uses = uses f left_request in
            let right_uses = uses x right_request in
            (* normalize application and terminal probabilities *)
            let z = lse terminal_probability application_probability in
            let terminal_probability = exp (terminal_probability-.z) in
            let application_probability = exp (application_probability-.z) in
            (* mix together the terminal and application uses *)
            { application_counts = application_probability*.(1.0+.left_uses.application_counts+.right_uses.application_counts);
              terminal_counts = terminal_probability+.application_probability*.(left_uses.terminal_counts+.right_uses.terminal_counts);
              use_counts = Array.init number_terminals
                (fun j -> application_probability*.(left_uses.use_counts.(j)+.right_uses.use_counts.(j))
                +. (if j = offset then terminal_probability else 0.0));
              possible_counts = Array.init number_terminals
                (fun j -> application_probability*.(left_uses.possible_counts.(j)+.right_uses.possible_counts.(j))
                +. (if List.mem j distractors then terminal_probability else 0.0));
            }
      in Hashtbl.add use_map (i,request) u; u
  in 
  let applications = ref smoothing in
  let terminals = ref smoothing in
  let terminal_uses = Array.make number_terminals smoothing in
  let terminal_chances = Array.make number_terminals smoothing in
  List.iter (fun ((i,request),w) -> 
            let u = uses i request in
            applications := w*.u.application_counts +. !applications;
            terminals := w*.u.terminal_counts +. !terminals;
            for j = 0 to (number_terminals-1) do
             terminal_uses.(j) <- w*.u.use_counts.(j) +. terminal_uses.(j);
             terminal_chances.(j) <- w*.u.possible_counts.(j) +. terminal_chances.(j);
            done)
    corpus;
  let log_application = log (!applications/.(!applications +. !terminals)) in
  let distribution = List.fold_left (fun a (i,(_,_,o)) -> 
                                    let p = log (terminal_uses.(o)) -. log (terminal_chances.(o))
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
  let corpus = List.map (fun (i,l) -> (i,exp l)) @@ 
    merge_a_list lse task_posteriors in
  fit_grammar smoothing grammar dagger program_types likelihoods corpus

(* various built-in primitives *)
let c_S = Terminal("S", canonical_type @@  
                  make_arrow (make_arrow t1 (make_arrow t2 t3))
                             (make_arrow (make_arrow t1 t2)
                                         (make_arrow t1 t3)),
                  Obj.magic (ref (fun f g x -> (f x) (g x))));;
let c_B = Terminal("B", canonical_type @@ 
                  make_arrow (make_arrow t2 t3)
                             (make_arrow (make_arrow t1 t2)
                                         (make_arrow t1 t3)),
                  Obj.magic (ref (fun f g x -> f (g x))));;
let c_C = Terminal("C",  canonical_type @@ 
                  make_arrow (make_arrow t1 (make_arrow t2 t3))
                             (make_arrow t2 (make_arrow t1 t3)),
                  Obj.magic (ref (fun f g x -> (f x) g)));;
let c_K = Terminal("K", canonical_type @@ 
                   make_arrow t1 (make_arrow t2 t1),
                   Obj.magic (ref (fun x _ -> x)));;
let c_I = Terminal("I", canonical_type @@ 
                   make_arrow t1 t1,
                   Obj.magic (ref (fun x -> x)));;
let combinatory_library = 
  make_flat_library [c_S;c_B;c_C;c_K;c_I]


let c_one = Terminal("1",make_ground "int",Obj.magic (ref 1));;
let c_zero = Terminal("0",make_ground "int",Obj.magic (ref 0));;
let c_plus = Terminal("+",
                     make_arrow (make_ground "int") (make_arrow (make_ground "int") (make_ground "int")),
                     Obj.magic (ref (fun x y ->x+y )));;
let c_times = Terminal("*",
                     make_arrow (make_ground "int") (make_arrow (make_ground "int") (make_ground "int")),
                     Obj.magic (ref (fun x y ->x*y )));;

let polynomial_library = 
  make_flat_library [c_S;c_B;c_C;c_I;c_one;c_zero;c_plus;c_times;];;


let string_of_library (log_application,distribution) = 
  let bindings = ExpressionMap.bindings distribution in
  String.concat "\n"
    ((string_of_float (exp log_application))::
     (List.map (fun (e,(w,_)) -> Printf.sprintf "\t %f \t %s " w (string_of_expression e)) 
        bindings));;

let all_terminals = [c_K;c_S;c_B;c_C;c_I;c_one;c_zero;c_plus;c_times;] |> 
                    List.map (fun e -> (string_of_expression e,e))

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
                else List.assoc name all_terminals))
    else raise (Failure ("expression_of_string: "^s))
  in read ()

let test_library () = 
  ["I";"((C +) 1)";"(K (+ (0 S)))"] |> List.map 
    (fun s -> print_string (string_of_expression @@ expression_of_string s); print_newline ());;


(* test_library ();; *)
