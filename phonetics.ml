open Expression
open Type


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

let make_consonant (n : string) (f : consonant) : expression = 
  Terminal(n,make_ground "phone",Obj.magic @@ ref f)

let make_vowel (n : string) (v : vowel) : expression = 
  Terminal(n,make_ground "phone",Obj.magic @@ ref v)

(* library entries *)
let c_s = make_consonant "s" (Alveolar,Fricative,Unvoiced);;
let c_z = make_consonant "z" (Alveolar,Fricative,Voiced);;
let c_t = make_consonant "t" (Alveolar,Stop,Unvoiced);;
let c_d = make_consonant "d" (Alveolar,Stop,Voiced);;
let v_i = make_vowel "i" V_i;;
let v_ae = make_vowel "ae" V_ae;;

let phones = [c_s;c_z;c_t;c_d;
              v_i;v_ae;]
