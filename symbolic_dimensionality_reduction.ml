open Expression
open Type
open Library
open Utils
open Task
open Enumerate


let make_decoder dagger i j = 
  (* arbitrary cutoffs *)
  let max_wild = 4 in
  let min_tame = 0 in
  let d = antiunify_expressions dagger i j in
  let rec count_terminals = function
    | Terminal(n,_,_) when n = "?" -> (1,0)
    | Application(f,x) -> 
      let (a,b) = count_terminals f
      and (p,q) = count_terminals x in
      (a+p,b+q)
    | _ -> (0,1)
  in
  let (number_wild, number_tame) = count_terminals d in
  if number_wild < max_wild && number_tame > min_tame
  then Some(insert_expression dagger d)
  else None

let potential_decoders dagger solutions = 
  (* consider each pair of frontiers *)
  let potentials = solutions |> map_list (function
    | [] -> IntSet.empty
    | [_] -> IntSet.empty
    | (t :: rest) -> List.concat rest |> List.fold_left (fun a other -> 
      t |> List.fold_left (fun b this -> 
            match make_decoder dagger this other with
            | None -> b
            | Some(d) -> IntSet.add d b) a) IntSet.empty) in
  (* coalesced potentials *)
  let potentials = potentials |> List.fold_left IntSet.union IntSet.empty in
  Printf.printf "Computed %i pairwise decoders" @@ IntSet.cardinal potentials;
  print_newline ();
  (* only keep those that can be used in all of the tasks *)
  let candidates = potentials |> IntSet.filter (fun c -> 
    solutions |> List.for_all (List.exists (can_match_wildcards dagger c))) in
  Printf.printf "Computed %i candidate decoders" @@ IntSet.cardinal candidates;
  print_newline ();
  IntSet.elements candidates

let decode_likelihood grammar dagger paths i = 
  let rec score_path r e = function
    | L :: p -> begin
      match e with
      | Application(l,_) -> score_path r l p
      | Terminal(q,_,_) when q.[0] = '?' -> 0.0
      | _ -> neg_infinity
    end
    | R :: p -> begin
      match e with
      | Application(_,x) -> score_path r x p
      | Terminal(q,_,_) when q.[0] = '?' -> 0.0
      | _ -> neg_infinity
    end
    | [] -> match likelihood_option grammar r e with
      | None -> neg_infinity
      | Some(l) -> l
  in
  let e = extract_expression dagger i in
  List.fold_left (fun a (path,r) -> a+.score_path r e path) 0. paths

let decoder_posterior dagger grammar request solutions decoder = 
  let modified_grammar = (fst grammar,ExpressionMap.add empty_wildcard (0.,t1) @@ snd grammar) in
  let manifold = extract_expression dagger decoder in
  Printf.printf "Posterior: %s" @@ string_of_expression manifold;
  print_newline ();
  let prior =
    safe_get_some "decoder_posterior: prior" @@ 
    likelihood_option modified_grammar request manifold in
  print_float prior; print_newline ();
  let paths = wild_types dagger request decoder in
  print_int @@ List.length paths; print_newline ();
  let likelihood = solutions |> List.fold_left (fun l frontier -> 
      let term = frontier |> List.fold_left (fun a i -> 
          if can_match_wildcards dagger decoder i 
          then lse a (decode_likelihood grammar dagger paths i)
          else a) neg_infinity in
      l +. term) 0.0 in
  prior+.likelihood

let best_decoder dagger grammar request solutions = 
  let decoders = potential_decoders dagger solutions in
  let decoder_scores = List.map (decoder_posterior dagger grammar request solutions) decoders in
  fst @@ List.hd @@ List.sort (fun (_,p) (_,q) -> compare q p) @@ List.combine decoders decoder_scores

let reduce_symbolically base_grammar posterior_grammar frontier_size tasks = 
  let (frontiers,dagger) = enumerate_frontiers_for_tasks posterior_grammar frontier_size tasks in
  print_string "Scoring programs...";
  print_newline ();
  let program_scores = score_programs dagger frontiers tasks in
  let request = (List.hd tasks).task_type in
  let task_solutions = program_scores |> List.map 
                         (compose (List.map fst) @@ List.filter (fun (_,s) -> is_valid s))
                       |> List.filter (fun s -> List.length s > 0)
  in 
  Printf.printf "%i / %i tasks solved." (List.length task_solutions) (List.length tasks);
  print_newline ();
  let d = time_it "Found decoder"
      (fun () -> best_decoder dagger base_grammar request task_solutions) in
  extract_expression dagger d
