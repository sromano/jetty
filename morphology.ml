open Phonetics
open Ec
open Task
open Library
open Expression
open Type
open Utils
open Symbolic_dimensionality_reduction

(* most common nouns produced by thirty months old *)
let top_nouns = [
  "b c l";
  "b ue b ue l z";
  "t sh i z";
  "k uu k i";
  "m I l k";
  "p ae n t s";
  "s a k";
  "a r m";
  "f uu t";
  "n ow z";
  "k i z";
  "l aj t";
  "w a t ue r";
  "s ow p";
  "d c r";
  "b ej b i";
  "b ae th";
  "b ue r d";
  "h c r s";
  "b aj s I k ue l";
]

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
  let lambda = 2.0 in
  let alpha = 1. in
  let frontier_size = 20000 in
  let g = ref @@ make_flat_library @@ phonetic_terminals in 
  let tasks = 
    top_nouns |> List.map make_word_task in
  for i = 1 to 9 do
    Printf.printf "\n \n \n Iteration %i \n" i;
    let g1 = lower_bound_refinement_iteration ("log/iter_"^string_of_int i)
        lambda alpha frontier_size tasks (!g) in
    g := g1
  done;
  let decoder =
    reduce_symbolically (make_flat_library @@ phonetic_terminals) !g frontier_size tasks in
  Printf.printf "Decoder: %s\n" (string_of_expression decoder)
;;


morphology ();;
