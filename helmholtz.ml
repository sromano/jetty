open Core.Std


open Task
open Expression
open Type
open Utils
open Library
open Compress
open Frontier
open Enumerate

let fit_grammars_for_tasks frontier_size g0 tasks =
  let (frontiers,dagger) = enumerate_frontiers_for_tasks g0 frontier_size tasks in
  let requests = frontier_requests frontiers in
  let type_array = infer_graph_types dagger in
  let likelihoods = program_likelihoods g0 dagger type_array requests in
  print_string "Scoring programs... \n";
  let program_scores = score_programs dagger frontiers tasks in

  List.map2_exn tasks program_scores ~f:(fun task scores ->
      (* did we miss ? *)
      if not (List.exists scores ~f:(fun (_,s) -> s > log (0.999))) then None else
        let explanations = List.map scores ~f:(fun (j,_) -> j) in
        let corpus = List.map explanations ~f:(fun j ->
            ((j,task.task_type), exp (Hashtbl.find_exn likelihoods (j,task.task_type)))) in
        let specializedGrammar =
          fit_grammar 0.01 g0 dagger type_array likelihoods corpus
        in
(*        let oldExplanationLikelihoods = List.map explanations ~f:(fun j ->
            get_some @@ likelihood_option g0 task.task_type (extract_expression dagger j)) in
        let newExplanationLikelihoods = List.map explanations ~f:(fun j ->
          get_some @@ likelihood_option specializedGrammar task.task_type (extract_expression dagger j)) in
Printf.printf "%s: %f vs %f\n" (task.name) (lse_list oldExplanationLikelihoods) (lse_list newExplanationLikelihoods); *)
        Some(specializedGrammar))

let make_training_data frontier_size g0 tasks features =
  let specialized = fit_grammars_for_tasks frontier_size g0 tasks in
  List.filter_map (List.zip_exn specialized features) ~f:(fun (g,fs) ->
      match g with
      |None -> None
      |Some((lp,l)) ->
        let targetOutput = List.map l ~f:(fun (_,(lp,_)) -> lp) in
        Some((fs,lp::targetOutput)))

let export_testing_data features =
  let code =
    String.concat ~sep:",\n" @@ List.map features ~f:(fun xs ->
      let xs = List.map ~f:string_of_int xs in
      "[" ^ String.concat ~sep:"," xs ^ "]")
  in
  Out_channel.write_all "testingData.py" ~data:("testingData = ["^code^"]");;

let export_training_data frontier_size grammar tasks features =
  let training = make_training_data frontier_size grammar tasks features in
  let code =
    String.concat ~sep:",\n" @@ List.map training ~f:(fun (xs,ys) ->
      let xs = List.map ~f:string_of_int xs in
      let ys = List.map ~f:string_of_float ys in
      "([" ^ String.concat ~sep:"," xs ^ "],[" ^ String.concat ~sep:"," ys ^ "])")
  in
  Out_channel.write_all "trainingData.py" ~data:("trainingData = ["^code^"]");;

let evaluate_grammar_for_task frontier_size grammar task =
  let (frontiers,dagger) = enumerate_frontiers_for_tasks grammar frontier_size [task] in
  let scores = List.hd_exn @@ score_programs dagger frontiers [task] in
  if List.exists scores ~f:(fun (_,s) -> s > log (0.999)) then
    let explanations = List.map scores ~f:(fun (j,_) -> j) in
    Some(List.map explanations ~f:(fun j ->
        get_some @@ likelihood_option grammar task.task_type (extract_expression dagger j))
         |> lse_list)
  else 
    None



let train_recognition_model frontier_size grammar tasks features =
  export_training_data frontier_size grammar tasks features;
  ignore(Sys.command "python recognition.py train");
  export_testing_data features;
  let predictions = command_output "python recognition.py test" |>
                    String.split ~on:'\n'  |>
                    List.filter ~f:(fun p -> not (p = "")) |>
                    List.map ~f:Float.of_string 
  in
  (* split the predictions into the segments that correspond to each task *)
  let outputDimensionality = 1 + List.length (snd grammar) in
  let customGrammars : library list = 
    (1--(List.length tasks)) |>
    List.map ~f:(fun taskIndex -> List.take (List.drop predictions ((taskIndex-1)*outputDimensionality)) outputDimensionality)
    |> List.map ~f:(function | pa::pp -> (pa,List.map2_exn pp (snd grammar) ~f:(fun p (e,(_,t)) -> (e,(p,t)))))
  in
  let customLikelihoods = List.map2_exn customGrammars tasks ~f:(evaluate_grammar_for_task frontier_size) |>
  List.filter ~f:is_some |> List.map ~f:get_some in
  let originalLikelihoods = List.filter_map tasks ~f:(evaluate_grammar_for_task frontier_size grammar) in
  Printf.printf "HIT: %d (new) vs %d (old)\n" (List.length customLikelihoods) (List.length originalLikelihoods);
  Printf.printf "LL: %f (new) vs %f (old)\n" (avg customLikelihoods) (avg originalLikelihoods)
