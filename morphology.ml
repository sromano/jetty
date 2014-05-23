open Phonetics
open Ec
open Task
open Library
open Expression
open Type
open Utils
open Symbolic_dimensionality_reduction
open Bottom_up


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

let doubled_words = 
  top_nouns |> List.map (fun w -> w ^ " " ^ w)

let make_word_task word = 
  let e = make_phonetic word in
  let correct_phones : phone list = safe_get_some "make_work_task: None" @@ run_expression e in
  let prop = (fun e w -> 
    match e with
    | Terminal(_,TCon("phone",[]),p) -> 
    let p : phone = !(Obj.magic p) in
    if List.exists (phonetic_neighbors p) correct_phones
    then w
    else w-.10000.
    | _ -> w) in  
  { name = word; task_type = TCon("list",[make_ground "phone"]); 
    score = Seed(e); proposal = Some(prop); }


let morphology () = 
  let lambda = 2.0 in
  let alpha = 1. in
  let frontier_size = 2000 in
  let keep_size = 2000 in
  let g = ref @@ make_flat_library @@ phonetic_terminals in 
  let tasks = 
    doubled_words |> List.map make_word_task |> take 3 in
  for i = 1 to 9 do
    Printf.printf "\n \n \n Iteration %i \n" i;
    let g1 = backward_iteration ("log/iter_"^string_of_int i)
        lambda alpha frontier_size keep_size tasks (!g) in
    g := g1
  done;
(*  let decoder =
    reduce_symbolically (make_flat_library @@ phonetic_terminals) !g frontier_size tasks in
  Printf.printf "Decoder: %s\n" (string_of_expression decoder) *)
;;


morphology ();;
