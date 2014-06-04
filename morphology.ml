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


(* most common adjective stems produced by thirty months old *)
let top_adjectives = [
  "k ow l d";
  "d ue r t i";
  "h a t";
  "w E t";
  "b I g";
  "b r ow k ue n";
  "k l i n";
  "g uu d";
  "h E v i";
  "j ue k i";
  "h ue ng g r i";
  "l I t ue l";
  "ue s l i p";
  "d r aj";
  "c r ue n d zh";
  "h ue r t";
  "b ae d";
  "h ae p i";
  "r E d";
  "b l u";
]

(* have comparative/superlative form *)
let comparable_adjectives = 
  List.filter top_adjectives (* remove words without comparative form *)
    ~f:(not % List.mem ["b r ow k ue n";"g uu d";"ue s l i p";"h ue r t";])

let top_comparative =
  List.map comparable_adjectives ~f:(fun w -> w ^ " ue r")

let top_superlative =
  List.map comparable_adjectives ~f:(fun w -> w ^ " ue s t")

(* most common verb stems produced by thirty months old *)
let top_verbs = [
  "i t";
  "g ow";
  "f a l";
  "h ue g";
  "k I s";
  "w a k";
  "l ue v";
  "w a sh";
  "k r aj";
  "l uu k";
  "ow p ue n";
  "p l ej";
  "d r I ng k";
  "r i d";
  "s l i p";
  "s t a p";
  "b aj t";
  "b l ow";
  "b r ej k";
  "h I t";
]

(* remarkably regular *)
let top_gerunds =
  List.map top_verbs ~f:(fun v -> v ^ " I ng")

(* top verbs with case marking (3rd person singular present) *)
let top_case = [
  "i t s";
  "g ow z";
  "f a l z";
  "h ue g s";
  "k I s ue z";
  "w a k s";
  "l ue v z";
  "w a sh ue z";
  "k r aj z";
  "l uu k s";
  "ow p ue n z";
  "p l ej z";
  "d r I ng k s";
  "r i d z";
  "s l i p s";
  "s t a p s";
  "b aj t s";
  "b l ow z";
  "b r ej k s";
  "h I t s";
]

let top_past = [
  "ej t";
  "w E n t";
  "f E l";
  "h ue g d";
  "k I s t";
  "w a k t";
  "l ue v d";
  "w a sh t";
  "k r aj d";
  "l uu k t";
  "ow p ue n d";
  "p l ej d";
  "d r ae ng k";
  "r i d";
  "s l E p t";
  "s t a p t";
  "b I t";
  "b l u";
  "b r ow k";
  "h I t";
]

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
  ["a a"; "b c b c"; "s ow p s ow p"; "r I g z r I g z"; ]

let make_word_task word stem = 
  let word_parts = String.split word ' ' in
  let stem_parts = String.split stem ' ' in
  let e = make_phonetic word in
  let affix = make_phonetic @@ String.concat ~sep:" " @@ 
    List.drop word_parts @@ List.length stem_parts in
  let relevant_phones : phone list = safe_get_some "make_work_task: None" @@ 
    run_expression affix in
  let correct_phones : phone list = safe_get_some "make_work_task: None" @@ run_expression e in
  let prop = (fun e w -> 
    match e with
    | Terminal(_,TCon("phone",[]),p) -> 
    let p : phone = !(Obj.magic p) in
    if List.exists relevant_phones (phonetic_neighbors p)
    then w
    else w-.10000.
    | _ -> w) in  
  let ll e =
    match run_expression e with
    | Some(ps) when ps = correct_phones -> 0.0
    | _ -> Float.neg_infinity
  in
  let wl = String.length word in
(*   let prefixes = String.split word ' ' |> 
                 map_list (String.concat ~sep:" ") |> 
                 List.filter ~f:(fun s -> String.length s > 0 && String.length s < wl) |> 
                 List.map ~f:make_phonetic in
  let suffixes = String.split word ' ' |> List.rev |> 
                 map_list (fun l -> String.concat ~sep:" " @@ List.rev l) |> 
                 List.filter ~f:(fun s -> String.length s > 0 && String.length s < wl) |> 
                 List.map ~f:make_phonetic in *)
  let extras = [make_phonetic stem,0.] in
  { name = word; task_type = TCon("list",[make_ground "phone"]); 
    score = LogLikelihood(ll); proposal = Some(prop,extras); }

let pluralize = expression_of_string
  "((S @) ((B ((C cons) null)) ((B (transfer-voice /s/)) last-one))"
(*     "((S @1) ((B (transfer-voice /s/)) last-one))" *)

let morphology () = 
  let lambda = 1.5 in
  let alpha = 1. in
  let frontier_size = 1000 in
  let g = ref @@ make_flat_library phonetic_terminals (* load_library "log/super_1_grammar" *) in 
  let tasks = 
    List.map2_exn top_plural top_singular make_word_task in
 List.iter2_exn tasks (List.zip_exn top_singular top_plural) ~f:(fun t (s,p) -> 
    let grammar = modify_grammar !g t in
    let p = Application(pluralize, make_phonetic s) in
    Printf.printf "plural %s > %f\n " s (get_some @@ likelihood_option grammar (t.task_type @> t.task_type) pluralize);
    Printf.printf "%s > %f\n " s (get_some @@ likelihood_option grammar t.task_type p));
(*  for i = 1 to 10 do
    Printf.printf "\n \n \n Iteration %i \n" i;
    g := lower_bound_refinement_iteration ("log/super_"^string_of_int i)
      lambda alpha frontier_size tasks (!g)
  done; *)
(*   let decoder =
    reduce_symbolically (make_flat_library @@ phonetic_terminals) !g frontier_size frontier_size tasks in
  Printf.printf "Decoder: %s\n" (string_of_expression decoder) *)
;;


morphology ();;
