open Core.Std

open Utils
open Type
open Program

let unifying_expressions g environment request context : (program*tp*tContext*float) list =
  let candidates = g.library @ List.mapi ~f:(fun j t -> (Index(j),t,g.logVariable)) environment in
  let candidates = 
  List.filter_map ~f:(fun (p,t,ll) ->
        try
          let (t,context) = if not (is_index p) then instantiate_type context t else (t,context) in
        match arguments_and_return_of_type t with
        | (argument_types, return_type) -> 
          let newContext = unify context return_type request in
          Some(p, t, newContext,ll)
      with _ -> None) candidates
  in
  let z = List.map ~f:(fun (_,_,_,ll) -> ll) candidates |> lse_list in
  List.map ~f:(fun (p,t,k,ll) -> (p,t,k,ll-.z)) candidates


let rec enumerate_programs (g: grammar) (context: tContext) (request: tp) (environment: tp list) (depth: float) : (program*tContext*float) list =
  (*   Printf.printf "DEPTH: %f\n" depth; *)
  if depth < 0.0 then [] else
    match arguments_and_return_of_type request with
    | ([],_) -> (* not trying to enumerate functions *)
      unifying_expressions g environment request context |> 
      List.map ~f:(fun (candidate, candidate_type, context, ll) ->
          enumerate_applications g context candidate_type candidate environment (depth+.ll) |>
        List.map ~f:(fun (p,k,al) -> (p,k,ll+.al)))
      |> List.concat
    | (arguments,return) ->
      let newEnvironment = List.rev arguments @ environment in
      let ad_lambdas b = List.fold_left ~init:b ~f:(fun b _ -> Abstraction(b)) (1 -- List.length arguments) in
      enumerate_programs g context return newEnvironment depth |>
      List.map ~f:(fun (body, newContext, ll) -> (ad_lambdas body, newContext, ll))
and
  enumerate_applications (g: grammar) (context: tContext) (f_type: tp) (f: program) (environment: tp list) (depth: float) : (program*tContext*float) list =
  (* returns the log likelihood of the arguments! not the log likelihood of the application! *)
  match arguments_and_return_of_type f_type with
  | ([], _) -> (* not a function so we don't need any applications *)
    [(f, context, 0.0)]
  | (first_argument::rest_arguments, _) ->
    enumerate_programs g context first_argument environment depth |>
    List.map ~f:(fun (a,k,ll) ->
        let a = Apply(f,a) in
        let (applicationType,k) = chaseType k (right_of_arrow f_type) in
        enumerate_applications g k applicationType a environment (depth+.ll) |>
      List.map ~f:(fun (a,k,a_ll) -> (a,k,a_ll+.ll))) |>
    List.concat

let iterative_deepening_enumeration (g:grammar) (request:tp) (size:int) : (program list) =
  let rec deepen bound =
    let possibleSolutions = enumerate_programs g empty_context request [] bound in
    if List.length possibleSolutions<size then deepen (bound +. 1.0) else
      List.map ~f:(fun (p,_,_) -> p) possibleSolutions
  in
  deepen 1.0


type task =
  { name: string; task_type: tp;
    log_likelihood: program -> float;
  }

let supervised_task name ty examples =
  { name = name;
    task_type = ty;
    log_likelihood = (fun p ->
        let f = evaluate [] p in
        if List.for_all examples ~f:(fun (x,y) -> f x == y) then 0.0 else log 0.0)
  }

let score_programs_for_tasks programs tasks =
  List.map tasks ~f:(fun t ->
      let ss = List.map programs t.log_likelihood in
      if List.mem ss 0.0 then Printf.printf "HIT: %s\n" t.name else ();
      ss)

let get_solutions_for_tasks programs tasks : program list list =
  let scores = score_programs_for_tasks programs tasks in
  List.map scores ~f:(fun likelihoods ->
      List.zip_exn  programs likelihoods |> List.filter_map ~f:(fun (p,l) ->
        if l = 0.0 then Some(p) else None))
        
  

let polynomial_tasks =
  (0--9) |> List.map ~f:(fun a ->
      (0--9) |> List.map ~f:(fun b ->
          (0--9) |> List.map ~f:(fun c ->
              let examples = List.map (0--5) ~f:(fun x -> (x, a*x*x + b*x + c)) in
              let n = Printf.sprintf "(%i x^2 + %i x + %i)" a b c in
              supervised_task n (tint @> tint) examples)))
  |> List.concat |> List.concat


let arithmetic_grammar =
  primitive_grammar [ primitive "k0" tint 0;
                      primitive "k1" tint 1;
                      primitive "+" (tint @> tint @> tint) (+);
                      primitive "*" (tint @> tint @> tint) ( * );
                      primitive "apply" (t0 @> (t0 @> t1) @> t1) (fun x f -> f x);]



