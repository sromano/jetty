open Core.Std

open Phonetics
open Ec
open Task
open Library
open Expression
open Type
open Utils
open Symbolic_dimensionality_reduction
open Em


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

(* most common singular nouns produced by thirty months old *)
let top_singular = [
  "b c l";
  "b ue b ue l";
  "t sh i z";
  "k uu k i";
  "m I l k";
(*   "p ae n t s"; *)
  "s a k";
  "a r m";
(*   "f uu t"; *)
  "n ow z";
  "k i z";
  "l aj t";
(*   "w a t ue r"; *)
  "s ow p";
  "d c r";
  "b ej b i";
  "b ae th";
  "b ue r d";
  "h c r s";
  "b aj s I k ue l";
]

(* most common singular nouns produced by thirty months old *)
let top_plural = [
  "b c l z";
  "b ue b ue l z";
  "t sh i z ue z";
  "k uu k i z";
  "m I l k s";
(*   "p ae n t s"; *)
  "s a k s";
  "a r m z";
(*   "f uu t"; *)
  "n ow z ue z";
  "k i z ue z";
  "l aj t s";
(*   "w a t ue r"; *)
  "s ow p s";
  "d c r z";
  "b ej b i z";
  "b ae th s";
  "b ue r d z";
  "h c r s ue z";
  "b aj s I k ue l z";
]

let doubled_words = 
  ["a a"; "b c b c"; "s ow p s ow p"; "r I g z r I g z"; "b aj s I k ue l b aj s I k ue l"]

let make_word_task word = 
  let e = make_phonetic word in
  let correct_phones : phone list = safe_get_some "make_work_task: None" @@ run_expression e in
  let prop = (fun e w -> 
    match e with
    | Terminal(_,TCon("phone",[]),p) -> 
    let p : phone = !(Obj.magic p) in
    if List.exists correct_phones (phonetic_neighbors p)
    then w
    else w-.10000.
    | _ -> w) in  
  { name = word; task_type = TCon("list",[make_ground "phone"]); 
    score = Seed(e); proposal = Some(prop); }


let morphology () = 
  let lambda = 1.5 in
  let alpha = 1. in
  let frontier_size = 200000 in
  let keep_size = 10000 in
  let g = ref @@ make_flat_library phonetic_terminals (* load_library "log/iter_2_grammar" *) in 
  let tasks = 
    List.map doubled_words (* (top_singular @ top_plural) *) make_word_task in
  for i = 1 to 5 do
    Printf.printf "\n \n \n Iteration %i \n" i;
    let g1 = backward_iteration ("log/morphology_"^string_of_int i)
        lambda alpha frontier_size keep_size tasks (!g) in
    g := g1
  done;
 let decoder =
    reduce_symbolically (make_flat_library @@ phonetic_terminals) !g 10000 1000 tasks in
  Printf.printf "Decoder: %s\n" (string_of_expression decoder)
;;


morphology ();;
