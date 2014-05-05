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
  V_i | V_I | V_ej | V_ae | V_ue | V_v | V_aj | V_aw | V_a | V_u | V_uu | V_ow | V_c | V_cj

(* phonemes *)
type phone = Vowel of vowel | Consonant of consonant

let make_phonetic (n : string) : string = "/"^n^"/"

let make_consonant (n : string) (f : consonant) : expression = 
  Terminal(make_phonetic n,make_ground "phone",Obj.magic @@ ref @@ Consonant(f))

let make_vowel (n : string) (v : vowel) : expression = 
  Terminal(make_phonetic n,make_ground "phone",Obj.magic @@ ref @@ Vowel(v))

(* library entries *)
let c_p = make_consonant "p" (Bilabial,Stop,Unvoiced);;
let c_b = make_consonant "b" (Bilabial,Stop,Voiced);;
let c_f = make_consonant "f" (LabialDental,Fricative,Unvoiced);;
let c_v = make_consonant "v" (LabialDental,Fricative,Voiced);;
let c_th = make_consonant "th" (Interdental,Fricative,Unvoiced);;
let c_Th = make_consonant "Th" (Interdental,Fricative,Voiced);;
let c_ut = make_consonant "ut" (Alveolar,Approximant,Voiced);;
let c_q = make_consonant "?" (Glottal,Stop,Unvoiced);;
let c_h = make_consonant "h" (Glottal,Fricative,Unvoiced);;
let c_s = make_consonant "s" (Alveolar,Fricative,Unvoiced);;
let c_z = make_consonant "z" (Alveolar,Fricative,Voiced);;
let c_sh = make_consonant "sh" (AlveolarPalatal,Fricative,Unvoiced);;
let c_zh = make_consonant "zh" (AlveolarPalatal,Fricative,Voiced);;
let c_j = make_consonant "j" (Palatal,Approximant,Voiced);;
let c_t = make_consonant "t" (Alveolar,Stop,Unvoiced);;
let c_d = make_consonant "d" (Alveolar,Stop,Voiced);;
let c_r = make_consonant "r" (Alveolar,Approximant,Voiced);;
let c_ng = make_consonant "ng" (Velar,Nasal,Voiced);;
let c_n = make_consonant "n" (Alveolar,Nasal,Voiced);;
let c_m = make_consonant "m" (Bilabial,Nasal,Voiced);;
let c_k = make_consonant "k" (Velar,Stop,Unvoiced);;
let c_g = make_consonant "g" (Velar,Stop,Voiced);;
let c_uw = make_consonant "uw" (Bilabial,Approximant,Unvoiced);;
let c_w = make_consonant "w" (Bilabial,Approximant,Voiced);;
let c_lo = make_consonant "lo" (Alveolar,LateralApproximate,Unvoiced);;
let c_l = make_consonant "l" (Alveolar,LateralApproximate,Voiced);;
let v_ej = make_vowel "ej" V_ej;;
let v_ue = make_vowel "ue" V_ue;;
let v_i = make_vowel "i" V_i;;
let v_I = make_vowel "I" V_I;;
let v_v = make_vowel "v" V_v;;
let v_ae = make_vowel "ae" V_ae;;
let v_ow = make_vowel "ow" V_ow;;
let v_a = make_vowel "a" V_a;;
let v_aj = make_vowel "aj" V_aj;;
let v_aw = make_vowel "aw" V_aw;;
let v_c = make_vowel "c" V_c;;
let v_cj = make_vowel "cj" V_cj;;
let v_u = make_vowel "u" V_u;;
let v_uu = make_vowel "uu" V_uu;;

let phones = [c_s;c_z;c_t;c_d;c_r;c_n;c_m;c_k;c_g;c_w;c_l;
              v_a;v_ej;v_ue;v_i;v_ae;v_ow;]

let l_transfer_voice = Terminal("transfer-voice",
                                make_arrow (make_ground "phone")
                                  (make_arrow (make_ground "phone") (make_ground "phone")),
                                Obj.magic @@ ref @@ 
                                fun p1 p2 ->
                                match (p1,p2) with
                                | (Consonant(p,m,_), Consonant(_,_,v)) -> Consonant(p,m,v)
                                | _ -> p1
                               )

let phonetic_terminals = [c_S;c_B;c_C;c_I;
                         c_null;c_append;c_cons;c_last_one;
                         l_transfer_voice;]
                         @ phones

(* are 2 phonemes similar enough that we should consider using one to search for the other? *)
let phonetic_neighbors p1 p2 = 
  match (p1,p2) with
  | (Consonant(x1,y1,_),Consonant(x2,y2,_)) when x1 = x2 && y1 = y2 -> true
  | (Vowel(v1),Vowel(v2)) when v1 = v2 -> true
  | _ -> false

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

(* test_phonetics ();; *)
