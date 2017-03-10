open Core.Std

open Utils
open Type

type program =
  | Index of int
  | Abstraction of program
  | Apply of program*program
  | Primitive of unit ref * tp * string

let rec show_program = function
  | Index(j) -> string_of_int j
  | Abstraction(body) ->
    "(lambda "^show_program body^")"
  | Apply(p,q) ->
    "("^show_program p^" "^show_program q^")"
  | Primitive(_,_,n) -> n

let primitive n t p = Primitive(magical @@ ref p, t, n)

let rec evaluate (environment: 'b list) (p:program) : 'a =
  match p with
  | Abstraction(b) -> magical @@ fun argument -> evaluate (argument::environment) b
  | Index(j) -> magical @@ List.nth_exn environment j
  | Apply(f,x) -> (magical @@ evaluate environment f) (magical @@ evaluate environment x)
  | Primitive(thing,_,_) -> !(magical thing)

type grammar = Grammar of (program*tp) list

let primitive_grammar primitives =
  Grammar(List.map primitives ~f:(fun p -> match p with
      |Primitive(_,t,_) -> (p,t)))

let grammar_primitives g =  match g with |Grammar(l) -> l;;
let unifying_expressions g environment request context : (program*tp*tContext) list =
  let candidates = grammar_primitives g @ List.mapi ~f:(fun j t -> (Index(j),t)) environment in
  List.filter_map ~f:(fun (p,t) ->
      try
        match arguments_and_return_of_type t with
        | (argument_types, return_type) -> 
          let newContext = unify context return_type request in
          Some(p, t, newContext)
      with _ -> None) candidates


let rec enumerate_programs (g: grammar) (context: tContext) (request: tp) (environment: tp list) (depth: int) : (program*tContext) list =
  if depth = 0 then [] else
    match arguments_and_return_of_type request with
    | ([],_) -> (* not trying to enumerate functions *)
      unifying_expressions g environment request context |> 
      List.map ~f:(fun (candidate, candidate_type, context) -> enumerate_applications g context candidate_type candidate environment depth)
      |> List.concat
    | (arguments,return) ->
      let newEnvironment = List.rev arguments @ environment in
      let ad_lambdas b = List.fold_left ~init:b ~f:(fun b _ -> Abstraction(b)) (1 -- List.length arguments) in
      enumerate_programs g context return newEnvironment (depth - 1) |>
      List.map ~f:(fun (body, newContext) -> (ad_lambdas body, newContext))
and
  enumerate_applications (g: grammar) (context: tContext) (candidate_type: tp) (candidate: program) (environment: tp list) (depth: int) : (program*tContext) list =
  match arguments_and_return_of_type candidate_type with
  | ([], _) -> (* not a function so we don't need any applications *)
    [(candidate, context)]
  | (first_argument::rest_arguments, return) ->
    enumerate_programs g context first_argument environment (depth - 1) |>
    List.map ~f:(fun (a,k) -> (Apply(candidate,a),k)) |>
    List.map ~f:(fun (a,k) ->
        let (applicationType,k) = chaseType k (right_of_arrow candidate_type) in
        enumerate_applications g k applicationType a environment (depth - 1)) |>
    List.concat
    
let arithmetic_grammar =
  primitive_grammar [ primitive "k0" tint 0;
                      primitive "k1" tint 1;
                      primitive "+" (tint @> tint @> tint) (+)]

let () =
  let program = (Apply(Abstraction(Index(0)),(primitive "42" tint 42))) in
  Printf.printf "%s -  - %d\n" (show_program program) (evaluate [] program);

  enumerate_programs arithmetic_grammar empty_context (tint @> tint @> tint) [] 5 |>
  List.iter ~f:(fun (p,_) -> Printf.printf "%s\n" (show_program p))
