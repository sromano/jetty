open Expression
open Type
open Library
open Utils
open Task

let task_features dagger (log_application,library) tasks_and_solutions = 
  let program_types = infer_graph_types dagger in
  let requests = tasks_and_solutions |> List.fold_left (fun r (t,solutions) -> 
    solutions |> List.fold_left (fun a s -> 
          try
             let old = IntMap.find s a in
             if List.mem t.task_type old then a else IntMap.add s (t.task_type :: old) a
          with Not_found -> IntMap.add s [t.task_type] a) r) IntMap.empty in
  let likelihoods = program_likelihoods (log_application,library) dagger program_types requests in
  (* find all of the production features *)
  let production_features = ExpressionMap.bindings library |> List.mapi (fun i (e,(l,t)) -> 
    (insert_expression dagger e,(i,(l,t)))) in
  (* variables for holding expected counts *)
  let expected_applications = ref 0. in
  let expected_terminals = ref 0. in
  let expected_uses = Array.make (List.length production_features) 0. in
  (* fills in the above expected counts *)
  let rec count_uses w i r = 
    match extract_node dagger i with
    | ExpressionLeaf(_) -> begin
      expected_terminals := !expected_terminals +. w;
      try
        let offset = fst @@ List.assoc i production_features in
        expected_uses.(offset) <- expected_uses.(offset) +. w
      with Not_found -> ()
    end
    | ExpressionBranch(f,x) -> 
      let left_request = function_request r in
      let right_request = argument_request r program_types.(f) in
      try
        let offset = fst @@ List.assoc i production_features in
        let application_likelihood = log_application +.
        Hashtbl.find likelihoods (f,left_request) +. Hashtbl.find likelihoods (x,right_request) in
        (* cool hack, we get terminal likelihood by 
           subtracting application likelihood from total likelihood *)
        let z = Hashtbl.find likelihoods (i,r) in
        let terminal_likelihood = lde z application_likelihood in
        (* normalize *)
        let application_weight = exp (application_likelihood -. z) in
        let terminal_weight = exp (terminal_likelihood -. z) in
        (* record it all *)
        expected_applications := !expected_applications +. (w*.terminal_weight);
        expected_terminals := !expected_terminals +. (w*.application_weight);
        expected_uses.(offset) <- expected_uses.(offset) +. (w*.terminal_weight);
        (* recurse *)
        count_uses (w*.application_weight) f left_request;
        count_uses (w*.application_weight) x right_request
      with Not_found -> begin
          expected_applications := !expected_applications +. w;
          count_uses w f left_request;
          count_uses w x right_request
      end
  in
  tasks_and_solutions |> List.map (fun (t,solutions) -> 
    let weighted_solutions = solutions |> List.map 
                               (fun s -> Hashtbl.find likelihoods (s,t.task_type)) in
    let z = lse_list weighted_solutions in
    expected_applications := 0.;
    expected_terminals := 0.;
    Array.fill expected_uses 0 (Array.length expected_uses) 0.;
    List.iter2 (fun w s -> count_uses (exp (w-.z)) s t.task_type) weighted_solutions solutions;
    !expected_applications :: !expected_terminals :: Array.to_list expected_uses)
