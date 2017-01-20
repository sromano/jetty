open Core.Std

open Expression
open Type
open Utils
open Library
open Phonetics

type indexed =
  | Leaf of expression
  | Abs of indexed
  | App of indexed * indexed
  | Index of int

let rec get_application_chain = function
  | App(f,x) -> get_application_chain f @ [x]
  | t -> [t]

let rec get_type_chain = function
  | TCon(k,[t1;t2]) when k = "->" -> t1 :: get_type_chain t2
  | t -> [t]

let destination_type t = List.last_exn (get_type_chain t)

let indexed_likelihood (log_a,log_L,leaves) request i =
  let leaf_types = List.map ~f:infer_type leaves in
  let log_t = log (1.-. exp log_a -. exp log_L) in
  let rec likelihood c g r = function
    | App(f,x) ->
      let (argument_type,c) = makeTID c in
      let (left_request,c) = chaseType c (argument_type @> r) in
      let (left_likelihood,c) = likelihood c g left_request f in
      let (argument_type,c) = chaseType c argument_type in
      let (right_likelihood,c) = likelihood c g argument_type x in
      (left_likelihood+.right_likelihood+.log_a, c)
    | Abs(b) -> begin
      let (r,c) = chaseType c r in
      match r with
      | TCon(k,[t1;t2]) when k = "->" ->
        let (bl,c) = likelihood c (t1 :: g) t2 b in
        (log_L +. bl, c)
      | _ -> raise (Failure "index_likelihood: Abs")
      end
    | e ->
      (* a terminal of some sort *)
      let conflicts = List.length (List.filter leaf_types (can_unify r)) +
                      List.length (List.filter g ~f:(fun y -> can_unify r (fst (chaseType c y)))) in
      let ll = log_t -. log (Float.of_int conflicts) in
      (* update typing information *)
      match e with
      | Index(i) ->
        let c = unify c r (List.nth_exn g i) in
        (ll,c)
      | Leaf(l) ->
        let t = List.findi leaves ~f:(fun _ e -> 0 = compare_expression l e) |> get_some |>
                fst |> List.nth_exn leaf_types in
        let c = unify c r t in
        (ll,c)
      | _ -> raise (Failure "indexed_impossible")
  in fst @@ likelihood empty_context [] request i


let normalized_likelihood (log_a,log_L,leaves) request i =
  let leaf_types = List.map ~f:infer_type leaves in
  let destination_types = List.map ~f:destination_type leaf_types in
  let log_v = log (1.-. exp log_a -. exp log_L) in
  let rec likelihood c g r e =
    match (r,e) with
    | (TCon(k,[t1;t2]), Abs(w)) when k = "->" ->
      likelihood c (t1 :: g) t2 w
    | _ ->
      let leaf_conflicts =
        List.filter destination_types (can_unify r) in
      let ctx_conflicts =
        List.filter g (fun y -> can_unify r (fst (chaseType c y))) in
      let log_v = if List.is_empty ctx_conflicts
        then Float.neg_infinity else log_v in
      let log_L = if List.is_empty leaf_conflicts
        then Float.neg_infinity else log_L in
      let z = lse_list [log_v;log_L;log_a] in
      match e with
      | App(Abs(b),x) ->
      let (argument_type,c) = makeTID c in
      let (b_l,c) = likelihood c (argument_type :: g) r b in
      let (argument_type,c) = chaseType c argument_type in
      let (x_l,c) = likelihood c g argument_type x in
      (x_l+.b_l+.log_a-.z, c)
      | Index(j) ->
        let ll =
          log_v-.z -. log (Float.of_int @@ List.length ctx_conflicts) in
        (* update typing information *)
        let c = unify c r (List.nth_exn g j) in
        (ll,c)
      | _ -> (* application of terminal from library *)
        match get_application_chain e with
        | (Leaf(f) :: xs) ->
          let f_t = List.findi leaves ~f:(fun _ e -> 0 = compare_expression f e) |> get_some |>
                    fst |> List.nth_exn leaf_types in
          let (f_t, c) = instantiate_type c f_t in
          let alphas = List.rev @@ List.tl_exn @@ List.rev @@ get_type_chain f_t in
          let ll = log_a-.z-. log (Float.of_int @@ List.length leaf_conflicts) in
          List.fold2_exn alphas xs ~init:(ll,c)
            ~f:(fun (ll,c) a e ->
              let (a,c) = chaseType c a in
              let (all,c) = likelihood c g a e in
              (ll+.all,c))
        | _ -> raise (Failure "get_application_chain")
  in fst @@ likelihood empty_context [] request i


let phonetic_leaves = [c_null;c_append;c_cons;c_last_one;l_is_voiced;l_strident;] @ phones;;


let indexed_of_string s =
  let i = ref 0 in
  let rec read () =
    if !i < String.length s
    then (if s.[!i] = '('
          then (if s.[!i+1] = '%'
                then (incr i; incr i; incr i;
                      let b = read () in
                      incr i;
                      Abs(b))
                else (incr i;
                      let f = read () in
                      incr i;
                      let x = read () in
                      incr i;
                      App(f, x)))
          else (let j = ref (!i) in
                while !j < String.length s && s.[!j] <> ')' && s.[!j] <> ' ' do
                  incr j
                done;
                let name = String.sub s !i (!j - !i) in
                i := !j;
                if Char.is_digit name.[0]
                then Index(Int.of_string name)
                else try
                    Leaf(List.Assoc.find_exn !all_terminals name)
                  with _ -> raise (Failure ("not in all_terminals: "^name))))
    else raise (Failure ("expression_of_string: "^s))
  in read ()

let () =
  let i = indexed_of_string "(% ((@ 0) (((is-voiced ((cons /z/) null)) ((cons /s/) null)) (last-one 0))))" in
  let r = TCon("list",[make_ground "phone"]) @> TCon("list",[make_ground "phone"]) in
  Printf.printf "%f\n" (normalized_likelihood (log 0.5, log 0.3,phonetic_leaves) r i);;

