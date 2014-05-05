open Phonetics
open Ec
open Task
open Library
open Expression
open Type
open Utils

let make_word_task word = 
  let correct_phones : phone list = run_expression @@ make_phonetic word in
  let scoring_function = (fun e -> 
    match run_expression_for_interval 0.03 e with
    | Some(phones) when phones = correct_phones -> 0.0
    | _ -> neg_infinity) in
  let prop = (fun e w -> 
    match e with
    | Terminal(_,TCon("phone",[]),p) -> 
    let p : phone = !(Obj.magic p) in
    if List.exists (phonetic_neighbors p) correct_phones
    then w
    else w-.10000.
    | _ -> w) in  
  { name = word; task_type = TCon("list",[make_ground "phone"]); 
    score = scoring_function; proposal = Some(prop); }


let morphology () = 
  let g = ref @@ make_flat_library @@ phonetic_terminals in
  let tasks = 
    ["i t";"i t s";
     "ej m";"ej m z";
     "ej k";"ej k s";
     "ej g";"ej g z";
     "ow t";"ow t s";
     "i l";"i l z";
(* "d ae d";"d ae d z";
     "r ue n";"r ue n z";"w a k";"w a k s"; *)
    ] |> List.map make_word_task in
  for i = 1 to 15 do
    Printf.printf "\n \n \n Iteration %i \n" i;
    let g1 = lower_bound_refinement_iteration ("log/iter_"^string_of_int i) 0.15 1.0 20000 tasks (!g) in
    g := g1
  done
;;


morphology ();;
