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

type grammar = {
  logVariable: float;
  library: (program*tp*float) list;
}

let primitive_grammar primitives =
  {library = List.map primitives ~f:(fun p -> match p with
       |Primitive(_,t,_) -> (p,t, 0.0 -. (log (float_of_int (List.length primitives)))));
   logVariable = log 0.5
  }



let string_of_grammar g =
  string_of_float g.logVariable
