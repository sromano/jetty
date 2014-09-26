open Expression
open Type
open Library
open Utils
open Frontier
open Task

open Core.Std

(* symbolic dimensionality reduction with an assumption of added noise *)
(* with probability M, a program is sampled according to the current decoder *)
(* with probability 1-M, a program is sampled from the base grammar *)

(* minimum fraction of tasks that must use a decoder for it to be considered *)
let minimum_M = 0.6;;


(* actually a lower bound on the likelihood *)
let noisy_decoder_likelihood dagger requested_type grammar d solutions = 
  let decoder_type = infer_type @@ extract_expression dagger d in
  let decoder_type = instantiated_type decoder_type (TID(next_type_variable requested_type)
                                                     @> requested_type) in
  match decoder_type with
  | Some(TCon(k,[argument_type;_])) when k = "->" -> 
    (* argument likelihoods *)
    let al = solutions |> List.map ~f:(fun (programs,_) -> 
      List.fold_left programs ~init:Float.neg_infinity
      ~f:(fun l p -> 
         match extract_expression_node dagger p with
         | ExpressionBranch(f,x) when f = d -> 
           lse l (likelihood_option grammar argument_type (extract_expression dagger x) |> 
                  safe_get_some "noisy_decoder_likelihood")
(*                   Option.value ~default:Float.neg_infinity) *)
         | _ -> l)) in
    (* count the number of uses of the decoder *)
    let decoder_uses = List.count al ~f:is_valid in
    let m = (Int.to_float decoder_uses) /. (Int.to_float @@ List.length solutions) in
    let log_m = log m in
    let log_1m = log (1. -. m) in
    let task_likelihood (_,e) a = 
      lse (log_m +. a) (log_1m +. e)
    in
    List.map2_exn ~f:task_likelihood solutions al |> 
    List.fold_left ~init:0. ~f:(+.)
  | _ -> Float.neg_infinity


let noisy_decoder_prior dagger g request d = 
  likelihood_option g (TID(next_type_variable request) @> request) (extract_expression dagger d)
  |> safe_get_some "noisy_decoder_prior"

let best_noisy_decoder dagger g request task_solutions = 
  let solutions = List.map task_solutions ~f:(fun ps -> 
    (ps, List.map ps ~f:(fun p -> 
          likelihood_option g request (extract_expression dagger p) |> 
          safe_get_some "best_noisy_decoder") |> lse_list)) in
  let task_decoders = List.map task_solutions 
      ~f:(List.fold_left ~init:Int.Set.empty ~f:(fun s p -> 
        match extract_expression_node dagger p with
        | ExpressionBranch(f,_) -> Int.Set.add s f
        | _ -> s)) in
  let candidate_decoders = Int.Set.union_list task_decoders in
  (* collect those decoders that are used at least minimum_M times *)
  let minimum_uses = Int.of_float @@ minimum_M *. (Int.to_float @@ List.length task_solutions) in
  let candidate_decoders = Int.Set.to_list @@ Int.Set.filter candidate_decoders
      ~f:(fun d -> minimum_uses < List.count task_decoders ~f:(fun ds -> Int.Set.mem ds d)) in
  (* pick the best decoder *)
  fst @@ List.hd_exn @@ List.sort ~cmp:(fun (_,p) (_,q) -> compare q p) @@ 
    parallel_map candidate_decoders ~f:(fun d -> 
    (d, noisy_decoder_prior dagger g request d +. noisy_decoder_likelihood dagger request g d solutions))  

let noisy_reduce_symbolically g0 g frontier_size tasks = 
  let (dagger, fs) = make_frontiers frontier_size frontier_size g tasks in
  let task_solutions = List.map fs (List.map ~f:fst) in
  let request = (List.hd_exn tasks).task_type in
  let d = time_it "Found noisy decoder"
      (fun () -> best_noisy_decoder dagger g0 request task_solutions) in
  extract_expression dagger d


(* enumerates frontiers that only use the given decoder *)
let decoder_frontiers g frontier_size tasks decoder = 
  let requested_type = (List.hd_exn tasks).task_type in
  let decoder_type = instantiated_type (infer_type decoder) (TID(next_type_variable requested_type)
                                                             @> requested_type) in
  match decoder_type with
  | Some(TCon(k,[argument_type;_])) when k = "->" -> 
    let tasks = List.map tasks ~f:(fun t -> 
        { name = t.name;
          task_type = argument_type;
          score = LogLikelihood(fun x -> task_likelihood t (Application(decoder,x)));
          proposal = t.proposal; }) in
    let (dagger, fs) = make_frontiers frontier_size frontier_size g tasks in
    let d = insert_expression dagger decoder in
    (dagger, List.map fs (List.map ~f:(fun (f,_) -> 
         insert_expression_node dagger (ExpressionBranch(d,f)))))
  | _ -> (make_expression_graph 10, List.map tasks ~f:(fun _ -> []))


(* When 1..(#tasks) are sampled randomly without replacement, *)
(* what is the expected decoder posterior? *)
let noisy_decoder_posterior g0 g frontier_size tasks decoder number_samples = 
  let requested_type = (List.hd_exn tasks).task_type in
  let (dagger, fs) = make_frontiers frontier_size frontier_size g tasks in
  let task_solutions = List.map fs ~f:(fun f -> Int.Set.of_list (List.map ~f:fst f)) in
  let (decoder_dagger, decoder_solutions) = decoder_frontiers g frontier_size tasks decoder in
  let task_solutions = List.map2_exn task_solutions decoder_solutions ~f:(fun set -> 
      List.fold_left ~init:set ~f:(fun s j -> 
          Int.Set.add s @@ insert_expression dagger @@ extract_expression decoder_dagger j)) |> 
                       List.map ~f:Int.Set.to_list in
  let task_solutions = List.map task_solutions ~f:(fun ps -> 
      (ps, List.map ps ~f:(fun p ->
           likelihood_option g0 requested_type (extract_expression dagger p) |>
           safe_get_some "noisy_decoder_posterior")
           |> lse_list)) in
  let prior = noisy_decoder_prior dagger g0 requested_type @@ 
    insert_expression dagger decoder in
  List.map (1 -- (List.length tasks)) ~f:(fun task_set_size ->
    avg @@ List.map (1 -- number_samples) ~f:(fun _ -> 
          let subset = random_subset task_solutions task_set_size in
          noisy_decoder_likelihood dagger requested_type g0 (insert_expression dagger decoder) subset))
