open Expression
open Type
open Library

(* consonants *)

type place = 
  | Bilabial
  | LabialDental
  | Interdental
  | Alveolar
  | AlveolarPalatal
  | Palatal
  | Velar
  | Glottal

type manner = 
  | Stop
  | Fricative
  | Nasal
  | Trill
  | Flap
  | Approximant
  | LateralApproximate
  | LateralFricative

type voice = Voiced | Unvoiced

type consonant = place * manner * voice


(* vowels *)
type vowel = 
  V_i | V_I | V_ej | V_e | V_ae | V_ue | V_v | V_aj | V_aw | V_a | V_u | V_uu | V_ow | V_c | V_cj

(* phonemes *)
type phone = Vowel of vowel | Consonant of consonant

let make_phonetic (n : string) : string = "/"^n^"/"

let make_consonant (n : string) (f : consonant) : expression = 
  Terminal(make_phonetic n,make_ground "phone",Obj.magic @@ ref f)

let make_vowel (n : string) (v : vowel) : expression = 
  Terminal(make_phonetic n,make_ground "phone",Obj.magic @@ ref v)

(* library entries *)
let c_s = make_consonant "s" (Alveolar,Fricative,Unvoiced);;
let c_z = make_consonant "z" (Alveolar,Fricative,Voiced);;
let c_t = make_consonant "t" (Alveolar,Stop,Unvoiced);;
let c_d = make_consonant "d" (Alveolar,Stop,Voiced);;
let v_i = make_vowel "i" V_i;;
let v_ae = make_vowel "ae" V_ae;;

let phones = [c_s;c_z;c_t;c_d;
              v_i;v_ae;]

(* creates a constant string of phonemes *)
let make_phonetic (s : string) : expression = 
  let rec slurp start_index = 
    if start_index >= String.length s
    then c_null
    else
      let end_index = try
          String.index_from s start_index ' ' 
        with
          Not_found -> String.length s
        | Invalid_argument(_) -> raise (Failure "slurp: invalid argument")
      in
      let substring = make_phonetic @@ String.sub s start_index (end_index - start_index) in
      try
        let p = phones |> List.find (fun p -> substring = string_of_expression p) in
        Application(Application(c_cons,p),
                    slurp (end_index+1))
      with Not_found -> raise (Failure("unknown phone: "^substring))
  in slurp 0

let test_phonetics () = 
  Printf.printf "%s\n" (string_of_expression @@ make_phonetic "s i d");
  Printf.printf "%s\n" (string_of_expression @@ make_phonetic "s ae d");
  Printf.printf "%s\n" (string_of_expression @@ make_phonetic "s i ae z");
  Printf.printf "%s\n" (string_of_expression @@ make_phonetic "z");
  Printf.printf "%s\n" (string_of_expression @@ make_phonetic "ae");;

test_phonetics ();;
