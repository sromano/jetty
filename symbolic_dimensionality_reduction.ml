open Expression
open Type
open Library
open Utils

let get_decoders dagger i : (int * int list) list = 
  let rec decoders arguments j = 
    (if List.length arguments > 0 then [(j,arguments)] else []) @
    (match extract_node dagger j with
     | ExpressionLeaf(_) -> []
     | ExpressionBranch(f,x) -> decoders (x::arguments) f)
  in decoders [] i

let decoder_argument_likelihood grammar decoder decoder_type requested_type arguments = 
  let rec argument_likelihood dt a = 
    match a with
    | [] -> raise (Failure "decoder_argument_likelihood: no arguments")
    | [b] -> (* WARNING: assumes that requested_type has no type variables *)
      get_some @@ likelihood_option grammar (make_arrow dt requested_type) b
    | b::bs -> 
      let b_type = infer_type b in
      let request = make_arrow dt @@ TID(next_type_variable dt) in
      let b_likelihood = get_some @@ likelihood_option grammar request b in
      let bs_likelihood = argument_likelihood (application_type dt b_type) bs in
      b_likelihood+.bs_likelihood
  in argument_likelihood decoder_type arguments

let decoder_posterior dagger grammar solutions decoder = 
  let decoder = extract_expression dagger decoder in
  let decoder_type = infer_type decoder in
  let prior =
    get_some @@ likelihood_option grammar (make_arrow t1 t2) decoder in
  let likelihood = solutions |> List.fold_left (fun l (t,arguments) -> 
      let a = List.map (List.map (extract_expression dagger)) arguments in
      let a_likes = a |> List.map (decoder_argument_likelihood grammar decoder decoder_type t) in
      l +. (lse_list a_likes)) 0.0 in
  prior+.likelihood

let best_decoder dagger grammar (solutions : (tp * int list) list) : int = 
  let decoders : (tp * (int * int list) list) list = solutions |> List.map (fun (t,s) ->
      (t, List.flatten @@ List.map (get_decoders dagger) s)) in
  (* only consider those decoders that are used in every task *)
  let candidates =
    remove_duplicates @@ List.flatten @@ List.map (compose (List.map fst) snd) decoders in
  let final_decoders = candidates |> List.filter (fun d -> 
    decoders |> List.for_all (fun (_,ds) -> List.mem d @@ List.map fst ds)) in
  (* take the best decoder *)
  snd @@ List.fold_left (fun (p1,d1) (p2,d2) -> if p1 > p2 then (p1,d1) else (p2,d2)) 
    (neg_infinity,insert_expression dagger c_I) @@ 
  List.map (fun d -> let solutions = decoders |> List.map (fun (t,s) -> 
    (t,s |> List.filter (fun (f,_) -> f = d) |> List.map snd)) in
             (decoder_posterior dagger grammar solutions d,d)) final_decoders
