
open Num
open Unix
open Utile
open Entiers
open Polynomes2

exception ToolNotFound of string
exception NotSupportedByMacOS

let fgbascii_path = Filename.concat Filename.current_dir_name "fgbascii"
let serveur__DMP__Lexp__GINT_path = Filename.concat Filename.current_dir_name "serveur__DMP__Lexp__GINT"
let singular_path = "Singular"
let magma_path = "magma"

(* ------------------------------------------------------------------------- *)
(*  Debugging                                                                *)
(* ------------------------------------------------------------------------- *)

let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)

let print_constr t =
  if Term.isRel t then failwith "Rel"
  else if Term.isVar t then failwith "Var"
  else if Term.isInd t then failwith "Ind"
  else if Term.isEvar t then failwith "Evar"
  else if Term.isMeta t then failwith "Meta"
  else if Term.isSort t then failwith "Sort"
  else if Term.isCast t then failwith "Cast"
  else if Term.isApp t then failwith "App"
  else if Term.isLambda t then failwith "Lambda"
  else if Term.isLetIn t then failwith "LetIn"
  else if Term.isProd t then failwith "Prod"
  else if Term.isConst t then failwith "Const"
  else if Term.isConstruct t then failwith "Construct"
  else if Term.isFix t then failwith "Fix"
  else if Term.isCoFix t then failwith "CoFix"
  else if Term.isCase t then failwith "Case"
  else if Term.isProj t then failwith "Proj"
  else failwith ""

(* ------------------------------------------------------------------------- *)
(*  Access Coq terms                                                         *)
(* ------------------------------------------------------------------------- *)

(* The contrib name is used to locate errors when loading constrs *)
let contrib_name = "gbarith_plugin"

let find_constant contrib dir s =
  Universes.constr_of_global (Coqlib.find_reference contrib dir s)

let init_constant dir s = find_constant contrib_name dir s

let fresh_id_in_env avoid id env =
  (* ids to be avoided *)
  let ids = (avoid@Termops.ids_of_named_context (Environ.named_context env)) in
  (* generate a new id *)
  Namegen.next_ident_away_in_goal id ids

let new_fresh_id avoid id gl =
  fresh_id_in_env avoid id (Proofview.Goal.env gl)

(* ------------------------------------------------------------------------- *)
(*  Groebner basis engines                                                   *)
(* ------------------------------------------------------------------------- *)

type version =
  | LT   (* Laurent Théry *)
  | JCF1 (* Jean-Charles Faugere *)
  | JCF2 (* Jean-Charles Faugere *)
  | SingularR
  | SingularZ
  | MagmaR
  | MagmaZ

let default_version = JCF1

let string_of_version v =
  match v with
  | LT -> "lt"
  | JCF1 -> "jcf1"
  | JCF2 -> "jcf2"
  | SingularR
  | SingularZ -> "singular"
  | MagmaR
  | MagmaZ -> "magma"

(* ------------------------------------------------------------------------- *)
(*  Positive                                                                 *)
(* ------------------------------------------------------------------------- *)

module CoqBinNums = struct
  let path = ["Coq"; "Numbers"; "BinNums"]
  let _xI : Term.constr lazy_t = lazy (init_constant path "xI")
  let _xO : Term.constr lazy_t = lazy (init_constant path "xO")
  let _xH : Term.constr lazy_t = lazy (init_constant path "xH")
  let _Z0 : Term.constr lazy_t = lazy (init_constant path "Z0")
  let _Zpos : Term.constr lazy_t = lazy (init_constant path "Zpos")
  let _Zneg : Term.constr lazy_t = lazy (init_constant path "Zneg")
end

let num_0 = Int 0
let num_1 = Int 1
let num_2 = Int 2
let num_10 = Int 10

(** Constructs a Coq positive from an OCaml num. *)
let rec cpos_of_onum (n : num) : Constr.t =
  if n </ num_0 then failwith "Not a positive number."
  else if n =/ num_1 then Lazy.force CoqBinNums._xH
  else if mod_num n num_2 =/ num_0 then Constr.mkApp (Lazy.force CoqBinNums._xO, [| cpos_of_onum (quo_num n num_2) |])
  else Constr.mkApp (Lazy.force CoqBinNums._xI, [| cpos_of_onum (quo_num n num_2) |])

(** Constructs an OCaml num from a Coq positive. *)
let rec onum_of_cpos (n : Constr.t) : num =
  if Constr.equal n (Lazy.force CoqBinNums._xH) then num_1
  else
    try
      let (constructor, args) = Term.destApp n in
      if Constr.equal constructor (Lazy.force CoqBinNums._xI) then num_1 +/ (onum_of_cpos args.(0) */ num_2)
      else if Constr.equal constructor (Lazy.force CoqBinNums._xO) then num_0 +/ (onum_of_cpos args.(0) */ num_2)
      else failwith "Not a valid Coq positive."
    with destKO -> failwith "Not a valid Coq positive."

(** Constructs a Coq integer from an OCaml num. *)
let rec cz_of_onum (n : num) : Constr.t =
  if n =/ num_0 then Lazy.force CoqBinNums._Z0
  else if n >/ num_0 then Constr.mkApp (Lazy.force CoqBinNums._Zpos, [| cpos_of_onum n |])
  else Constr.mkApp (Lazy.force CoqBinNums._Zneg, [| cpos_of_onum (abs_num n) |])

(** Constructs an OCaml num from a Coq integer. *)
let onum_of_cz (n : Constr.t) : num =
  if Constr.equal n (Lazy.force CoqBinNums._Z0) then num_0
  else
    try
      let (constructor, args) = Term.destApp n in
      if Constr.equal constructor (Lazy.force CoqBinNums._Zpos) then onum_of_cpos args.(0)
      else if Constr.equal constructor (Lazy.force CoqBinNums._Zneg) then minus_num (onum_of_cpos args.(0))
      else failwith "Not a valid Coq integer."
    with destKO -> failwith "Not a valid Coq integer."

(** Constructs a Coq positive from a number string in OCaml. *)
let cpos_of_ostring (str : string) : Constr.t =
  cpos_of_onum (num_of_string str)

(** Constructs a number string in OCaml from a Coq positive. *)
let ostring_of_cpos (n : Constr.t) : string =
  string_of_num (onum_of_cpos n)



(* ------------------------------------------------------------------------- *)
(*  Term                                                                     *)
(* ------------------------------------------------------------------------- *)

module CoqTerm = struct
  let path = ["GBArith"; "GBCompute"]
  let _Zero : Term.constr lazy_t = lazy (init_constant path "Zero")
  let _Const : Term.constr lazy_t = lazy (init_constant path "Const")
  let _Var : Term.constr lazy_t = lazy (init_constant path "Var")
  let _Opp : Term.constr lazy_t = lazy (init_constant path "Opp")
  let _Add : Term.constr lazy_t = lazy (init_constant path "Add")
  let _Sub : Term.constr lazy_t = lazy (init_constant path "Sub")
  let _Mul : Term.constr lazy_t = lazy (init_constant path "Mul")
  let _Pow : Term.constr lazy_t = lazy (init_constant path "Pow")
  let _lnil : Term.constr lazy_t = lazy (init_constant path "lnil")
  let _lceq : Term.constr lazy_t = lazy (init_constant path "lceq")
  let _LT : Term.constr lazy_t = lazy (init_constant path "LT")
  let _JCF1 : Term.constr lazy_t = lazy (init_constant path "JCF1")
  let _JCF2 : Term.constr lazy_t = lazy (init_constant path "JCF2")
  let _SingularR : Term.constr lazy_t = lazy (init_constant path "SingularR")
  let _SingularZ : Term.constr lazy_t = lazy (init_constant path "SingularZ")
  let _MagmaR : Term.constr lazy_t = lazy (init_constant path "MagmaR")
  let _MagmaZ : Term.constr lazy_t = lazy (init_constant path "MagmaZ")
end

type vname = string

type term =
  | Zero
  | Const of Num.num
  | Var of vname
  | Opp of term
  | Add of (term * term)
  | Sub of (term * term)
  | Mul of (term * term)
  | Pow of (term * int)

type lineq = term list

let rec string_of_term (t : term) : string =
  match t with
  | Zero -> "O"
  | Const n -> Num.string_of_num n
  | Var v -> v
  | Opp t -> "-(" ^ string_of_term t ^ ")"
  | Add (t1, t2) -> "(" ^ string_of_term t1 ^ " + " ^ string_of_term t2 ^ ")"
  | Sub (t1, t2) -> "(" ^ string_of_term t1 ^ " - " ^ string_of_term t2 ^ ")"
  | Mul (t1, t2) -> "(" ^ string_of_term t1 ^ " * " ^ string_of_term t2 ^ ")"
  | Pow (t1, t2) -> "(" ^ string_of_term t1 ^ " ^ " ^ string_of_int t2 ^ ")"

let numdom r =
  let r' = Ratio.normalize_ratio (ratio_of_num r) in
  num_of_big_int(Ratio.numerator_ratio r'),
  num_of_big_int(Ratio.denominator_ratio r')

(** Constructs a Coq term from an OCaml term. *)
let rec cterm_of_oterm (t : term) : Constr.t =
  match t with
    Zero -> Lazy.force CoqTerm._Zero
  | Const n ->
     let (m, d) = numdom n in
     Constr.mkApp (Lazy.force CoqTerm._Const, [| cz_of_onum m; cpos_of_onum d |])
  | Var v -> Constr.mkApp (Lazy.force CoqTerm._Var, [| cpos_of_ostring v |])
  | Opp t' -> Constr.mkApp (Lazy.force CoqTerm._Opp, [| cterm_of_oterm t' |])
  | Add (t1, t2) -> Constr.mkApp (Lazy.force CoqTerm._Add, [| cterm_of_oterm t1; cterm_of_oterm t2 |])
  | Sub (t1, t2) -> Constr.mkApp (Lazy.force CoqTerm._Sub, [| cterm_of_oterm t1; cterm_of_oterm t2 |])
  | Mul (t1, t2) -> Constr.mkApp (Lazy.force CoqTerm._Mul, [| cterm_of_oterm t1; cterm_of_oterm t2 |])
  | Pow (t', n) ->
     if n = 0 then cterm_of_oterm (Const (Int 1))
     else if n > 0 then Constr.mkApp (Lazy.force CoqTerm._Pow, [| cterm_of_oterm t'; cpos_of_onum (Int n) |])
     else failwith ("The exponent cannot be negative in the term: " ^ string_of_term t)

(** Constructs an OCaml term from a Coq term. *)
let rec oterm_of_cterm (t : Constr.t) : term =
  if Term.isConst t then
    match Global.body_of_constant (Univ.out_punivs (Term.destConst t)) with
      None -> failwith "Failed to find the definition of constant."
    | Some t' -> oterm_of_cterm t'
  else if Constr.equal t (Lazy.force CoqTerm._Zero) then Zero
  else
    try
      let (constructor, args) = Term.destApp t in
      if Constr.equal constructor (Lazy.force CoqTerm._Const) then Const ((onum_of_cz args.(0)) // (onum_of_cpos args.(1)))
      else if Constr.equal constructor (Lazy.force CoqTerm._Var) then Var (ostring_of_cpos args.(0))
      else if Constr.equal constructor (Lazy.force CoqTerm._Opp) then Opp (oterm_of_cterm args.(0))
      else if Constr.equal constructor (Lazy.force CoqTerm._Add) then Add (oterm_of_cterm args.(0), oterm_of_cterm args.(1))
      else if Constr.equal constructor (Lazy.force CoqTerm._Sub) then Sub (oterm_of_cterm args.(0), oterm_of_cterm args.(1))
      else if Constr.equal constructor (Lazy.force CoqTerm._Mul) then Mul (oterm_of_cterm args.(0), oterm_of_cterm args.(1))
      else if Constr.equal constructor (Lazy.force CoqTerm._Pow) then Pow (oterm_of_cterm args.(0), int_of_num (onum_of_cpos args.(1)))
      else failwith "Not a valid term (2)."
    with destKO -> failwith "Not a valid term (1)."

(** Constructs a Coq term list from an OCaml term list. *)
let rec clineq_of_olineq (t : lineq) : Constr.t =
  match t with
    [] -> Lazy.force CoqTerm._lnil
  | hd::tl -> Constr.mkApp (Lazy.force CoqTerm._lceq, [| cterm_of_oterm hd; clineq_of_olineq tl |])

(** Constructs an OCaml term list from a Coq term list. *)
let rec olineq_of_clineq (t : Constr.t) : lineq =
  if Term.isConst t then
    match Global.body_of_constant (Univ.out_punivs (Term.destConst t)) with
      None -> failwith "Failed to find the definition of constant."
    | Some t' -> olineq_of_clineq t'
  else if Constr.equal t (Lazy.force CoqTerm._lnil) then []
  else
    try
      let (constructor, args) = Term.destApp t in
      if Constr.equal constructor (Lazy.force CoqTerm._lceq) then (oterm_of_cterm args.(0) :: olineq_of_clineq args.(1))
      else failwith "Not a valid term list (2)."
    with destKO -> failwith "Not a valid term list (1)."



(* ------------------------------------------------------------------------- *)
(*  Copied from gb-keappa by Loïc Pottier except that                        *)
(*  1. inputfgb and outputfgb are moved to the system default temporary      *)
(*     directory,                                                            *)
(*  2. code of running external Groenber basis engines is moved to top-level *)
(*     functions,                                                            *)
(*  3. lire_coefouvarexp and lire_terme are modified to allow big integers,  *)
(*  4. Singular is added as a Groenber basis engine.                         *)
(* ------------------------------------------------------------------------- *)

let gbdir = "."

let version = ref default_version

let unix s =
  let r = Unix.system s in
  if r = r then ()
  else ()

let init_trace () =
  unix ("echo \"\" > " ^ gbdir ^ "/log_gb")

let trace s =
  unix ("echo \"" ^ s ^ "\n\" >> " ^ gbdir ^ "/log_gb")

(***********************************************************************)
(* Polynomes a coefficients fractionnaires *)
(* un polynome est represent'e par un polynome `a coefficient entiers
   et un entier (par lequel on divise tous les coefficients *)

type polyf = coef * poly (* denominateur, polynome *)
;;

(* normalise c et les coef de p, rend c positif *)
let norm_polyf (c,p) =
  let a = content p in
  let b = pgcd (abs_coef a) (abs_coef c) in
  let b = if (lt_coef c coef0) then opp_coef b else b in
    (div_coef c b, div_int p b)
;;

let plusPf (c1,p1) (c2,p2) =
  norm_polyf
    (mult_coef c1 c2,
     plusP (multP (Pint c2) p1) (multP (Pint c1) p2))
;;
let moinsPf (c1,p1) (c2,p2) =
  norm_polyf
    (mult_coef c1 c2,
     moinsP (multP (Pint c2) p1) (multP (Pint c1) p2))
;;

let multPf (c1,p1) (c2,p2) =
  norm_polyf
    (mult_coef c1 c2,
     multP p1 p2)
;;

let oppPf (c,p) =
  norm_polyf (c, oppP p)
;;

let puisPf (c,p) n =
 let rec aux n =
   if n=0
  then (coef1, (cf 1))
  else if n=1
  then (c,p)
  else multPf (c,p) (aux (n-1))
  in aux n
;;

let nvars = ref 0;;


(* terme vers couple (c,p) representant le polynome p/c *)

let rec term_polyf t  =  match t with
| Zero -> (coef1, (cf 0))
| Const r -> let (n,d) = numdom r in
   let d = ent_of_string (string_of_num d) in
   let n = ent_of_string (string_of_num n) in
               (d, Pint n)
| Var v -> let n = int_of_string v in
           nvars:= max (!nvars) n;
           (coef1,(x n))
| Opp t1 ->  oppPf (term_polyf t1)
| Add (t1,t2) -> plusPf (term_polyf t1) (term_polyf t2)
| Sub (t1,t2) -> moinsPf (term_polyf t1) (term_polyf t2)
| Mul (t1,t2) -> multPf (term_polyf t1) (term_polyf t2)
| Pow (t1,n) ->  puisPf (term_polyf t1) n
;;

(* polynoem recusrsif vers terme *)

let poly_term p =
  let rec aux p =
  match p with
   |Pint n -> Const (num_of_string (string_of_ent n))
   |Prec (v,coefs) ->
     let res = ref Zero in
     Array.iteri
      (fun i c ->
	 res:=Add(!res, Mul(aux c,
			    Pow (Var (string_of_int v),
				 i))))
      coefs;
     !res
  in aux p;;



(******************************************************************************

  La tactique Gb
*)

let rec pol_rec_to_sparse p v1 v2 =  (* v1 et v2 indices de début et de fin *)
  let d = v2-v1+1 in
    match p with
        Pint a ->
          if a= coef0
          then []
          else [a, Array.make (d+1) 0]
      |Prec(v,coefs)->
         let vp=Dansideal.gen d (v2-v+1) in (*j'aurais dit v2-v-1*)
         let res=ref [] in
           for i=(Array.length coefs)-1 downto 0 do
             res:= (Dansideal.plusP d
                      (Dansideal.multP d vp (!res))
                      (pol_rec_to_sparse coefs.(i) v1 v2));
           done;
           !res
;;

(* on inverse l'ordre des variables *)
let rec pol_sparse_to_rec n1 n2 p =
  List.fold_left (fun r (c,m)->
                    let mp = ref (Pint coef1) in
                      Array.iteri (fun i e ->
                                     if i>0 then
                                       mp:=(multP (!mp) (monome (n2-i+1) e)))
                        m;
                      plusP r (multP (Pint c) (!mp)))
    (Pint coef0)
    p
;;

let split_regexp rexp s =
  try (Str.split (Str.regexp rexp) s)
  with _ -> [s]

let replace e x s =
  Str.global_replace (Str.regexp e) x s

let rec rang x l =
  match l with
  |[] -> -1
  |y::l -> if x=y then 0 else 1+ (rang x l)

let read_string file =
    let st =open_in file in
    let ls=ref [] in
      (try
        (while true do
	   let c= (input_char st) in
           ls:=(String.make 1 c)::(!ls);
	 done)
       with End_of_file -> () | _ -> ((* pr "probleme dans le fichier";*) ()));
      close_in st;
      String.concat "" (List.rev (!ls))

let read_string2 file =
    let st =open_in file in
    let ls=ref [] in
      (try
        (while true do
	   let s= (input_line st) in
           ls:=(s^"\n")::(!ls);
	 done)
       with End_of_file -> () | _ -> ((* pr "probleme dans le fichier";*) ()));
      close_in st;
      String.concat "" (List.rev (!ls))



(***********************************************************************
  Lecture d' un fichier resultat de GB de JC Faugere, exemple:

#C ./serveur__DMP__Lexp__GINT.exe -pipe2 -read ../inputfgb
#C *** Gb 4.0.1360 for Windows (jcf@calfor.lip6.fr) ***
#C  Evaluation version (only)
#vars [t,z,x2,x1,e0,e1,e2]

#coeffring integer
#properties [GB, Lexp(7)]

#list
#C Dimension 3   Degree 2
[t-1*z^2*e1-1*z^2*e2-1*z*x2*e0-1*z*x1*e0-1*e0,z*x2*e1-1*z*x1*e2+x2^2*e0-1*x1^2*e0-1*e1+e2,z*x1*e1+z*x1*e2+x2*x1*e0+x1^2*e0-1*e2,x2*e2-1*x1*e1,e0^2,e0*e1,e0*e2,e1^2,e1*e2,e2^2]
#C Time 0.00 sec for computing a GB for a Lexp ordering(Buchberger)

*)


let lire_coefouvarexp s =
(*  trace ("coefouvar "^s);*)
  let (v,e)=
    (match (split_regexp "\\^" s) with
    |[v] -> (v,1)
    |[v;e] -> (v,int_of_string e)
    |_ -> failwith "lire_coefouvarexp" )
  in
  let (c,v,e) =
    try (Str.search_forward (Str.regexp "\\-*[0-9]+") v 0;
	 (Big_int.big_int_of_string v, "", 1))
    with _ ->
      if String.sub v 0 1 = "-"
      then (Big_int.big_int_of_int (-1),String.sub v 1 ((String.length v)-1),e)
      else (Big_int.big_int_of_int 1,v,e)
  in
(*  trace ("donne c="^(string_of_int c)^", v="^v^", e="^(string_of_int e));*)
  (c,v,e)

let lire_terme d vars s =
  let t = split_regexp "[\\*]" s in
  let lve= List.map lire_coefouvarexp  t in
  let cm = ref coef1 in
  let m = Array.make (d+1) 0 in
  List.iter
    (fun (c,v,e) ->
      cm:= mult_coef (!cm) (coef_of_big_int c);
      if v<>""
      then m.((rang v vars)+1)<- e
    )
    lve;
  let m = Dansideal.set_deg d m in
  (!cm),m

let lire_pol_fgb d vars s =
  let s = replace "-" "+-" s in
  let pol = List.map (lire_terme d vars)  (split_regexp "[\\+]" s) in
  pol

(** Parse the outputs from JCF1 and JCF2. *)
let lire_fgb s =
  if !version = JCF1
  then
    (let vars = !Dansideal.name_var in
    let d = List.length vars in
    let s = replace "[\n\t\r]" "" s in
    Str.search_forward (Str.regexp "#C Dimension.*#C Time") s 0;
    let s1 = Str.matched_string s in
    Str.search_forward (Str.regexp "\\[.+\\]") s1 0;
    let s2 = Str.matched_string s1 in
    let s2 = String.sub s2 1 ((String.length s2)-2) in
    let lpol = split_regexp "," s2 in
    List.map (lire_pol_fgb d vars) lpol
    )
  else (
    let vars = !Dansideal.name_var in
    let d = List.length vars in
    trace "lire_fgb commence";
    let s = replace "[\n\t\r]" "" s in
    trace "return vires";
    Str.search_forward (Str.regexp "GROBNER BASIS:.*") s 0;
    let s1 = Str.matched_string s in
    trace "GROBNER BASIS trouve";
    Str.search_forward (Str.regexp "\\[.+\\]") s1 0;
    let s2 = Str.matched_string s1 in
    let s2 = String.sub s2 1 ((String.length s2)-2) in
    let s2 = replace " " "" s2 in
    trace "base trouvee";
    let lpol = split_regexp "," s2 in
    trace "lpol calculee";
(*    trace ("resultat de fgb:\n"^s2);*)
    let res =  List.map (lire_pol_fgb d vars) lpol in
   trace ("res calcule");
    res
   )

let parse_singular_output filename =
  (* read lines from the output file *)
  let lines =
    let lines = ref [] in
    let ch = open_in filename in
    let _ =
      try
        while true do
	      let line = input_line ch in
          let poly =
            try
              let i = (String.index line '=') + 1 in
              let sub = String.sub line i (String.length line - i) in
              sub
            with _ ->
                 trace ("Error in parsing the output from Singular: " ^ line);
                 failwith "Error in parsing the output from Singular."
          in
          lines := poly::!lines;
	    done
      with End_of_file ->
        () in
    let _ = close_in ch in
    !lines in
  (* parse the output *)
  let res =
    let vars = !Dansideal.name_var in
    let d = List.length vars in
    List.map (lire_pol_fgb d vars) lines in
  res

let parse_magma_output filename =
  (* read lines from the output file *)
  let lines =
    let lines = ref [] in
    let ch = open_in filename in
    let pbegin = ref false in
    let pend = ref false in
    let buffer = ref "" in
    let add_buffer str = buffer := !buffer ^ str in
    let process_buffer () =
      if !buffer = "" then ()
      else
        let str = Str.global_replace (Str.regexp_string " ") "" !buffer in
        let _ = trace ("Poly: '" ^ str ^ "'") in
        lines := str::!lines; buffer := "" in
    let _ =
      try
        while not !pend do
	      let line = input_line ch in
          let _ = trace ("Line: '" ^ line ^ "'") in
          if line = "[" then pbegin := true
          else if line = "]" then (process_buffer(); pend := true)
          else if !pbegin then
            let str = String.trim line in
            if String.sub str (String.length str - 1) 1 = ","
            then (add_buffer (String.sub str 0 (String.length str - 1)); process_buffer())
            else add_buffer str
	    done
      with End_of_file ->
        () in
    let _ = close_in ch in
    !lines in
  (* parse the output *)
  let res =
    let vars = !Dansideal.name_var in
    let d = List.length vars in
    List.map (lire_pol_fgb d vars) lines in
  res


(* liste de polynomes lpol=p1,...,pn,
   echoue ou rend q1,...,qn,q tq 1=q1*p1+...+qn*pn+q*(1-zp)


   en general (B.Mourrain):
   exprimer 1=q1p1+...qnpn+q(1-zp)
   calculer la base de grobner de

   t*(1-zp)-e0, t*p1-e1,...,t*pn-en,ei*ej,t*ei

   avec t>>z>>x1,...,xm>>e0,e1,...,en
   et recuperer dedans un polynome
   t-q*e0-q1*e1-...-qn*en
   Voila.

*)

(** Returns a pair of variables and polynomials as the input of Groebner basis computation. *)
let compute_gb_input lpol p =
  (* lpol = p1, ..., pn *)
  let n = List.length lpol in
  let i = ref 0 in
  let m = (!nvars) in
  (*  t = m+2, ei = -i, z = m+1 *)
  (* lpol1 = t*p1-e1, ..., t*pn-en *)
  let lpol1 = List.map (fun pi ->
                        i := !i + 1;
                        plusP (multP (x (m+2)) pi) (oppP (x (-(!i)))))
                       lpol in
  (* polsup = t*(1-z*p) - e0 *)
  let polsup = (plusP (multP (x (m+2)) (plusP cf1 (oppP (multP (x (m+1)) p)))) (oppP (x 0))) in
  let lpol1 = polsup::lpol1 in
  let leiej = ref [] in
  (* ei*ej *)
  for j = 0 to n - 1 do
    for k = j + 1 to n do
      leiej := (multP (x (-j)) (x (-k)))::(!leiej);
    done;
  done;
  (* t*ei *)
  for j = 0 to n do
    leiej := (multP (x (-j)) (x (m+2)))::(!leiej);
  done;
  let lpol1 = (!leiej)@lpol1 in
  let lvar = ref [] in
  for i = 0 to n do lvar := (!lvar)@["e"^(string_of_int i)^""]; done;
  for i = 1 to m do lvar := ["x"^(string_of_int i)^""]@(!lvar); done;
  lvar := ["t1";"z"]@(!lvar);
  Dansideal.name_var := !lvar;
  let lpol1 = List.map (fun p -> pol_rec_to_sparse p (-n-1) (m+2)) lpol1 in
  let lpols = String.concat ", " (List.map Dansideal.stringP lpol1) in
  trace ("VARS: " ^ String.concat "," !lvar);
  trace ("POLS: " ^ lpols);
  (lvar, lpol1)

let string_of_gb lvar gb =
  let string_of_mon m =
    String.concat "*"
                  (List.filter
                     (fun str -> str <> "")
                     (List.mapi (fun i j ->
                                 (* the first element (i = 0) is the degree *)
                                 if i = 0 || j = 0 then ""
                                 else (List.nth !lvar (i-1)) ^
                                        (if j = 1 then ""
                                         else "^" ^ string_of_int j))
                                (Array.to_list m))) in
  let string_of_coef e =
    let str = string_of_ent e in
    if str = "1" then ""
    else if str = "-1" then "-"
    else str in
  let string_of_poly p =
    String.concat " + " (List.map (fun (e, m) ->
                                   string_of_coef e ^ string_of_mon m) p) in
  String.concat "\n" (List.map string_of_poly gb)

(** Computes the Groebner basis. *)
let compute_gb_output lpol lvar lpol1 =
  let n = List.length lpol in
  let m = (!nvars) in
  let inputfgb = Filename.temp_file "inputfgb_" "" in
  let outputfgb = Filename.temp_file "outputfgb_" "" in
  if !version = LT
  then
    let gb = Dansideal.buch (m+n+3) lpol1 in
    let _ =
      trace "OUTPUT GB:";
      trace (string_of_gb lvar gb) in
    gb
  else if !version = SingularR || !version = SingularZ
  then
    (* prepare the input to Singular *)
    let input_text =
      "ring r = " ^ (if !version = SingularR then "0" else "integer") ^ ", ("
      ^ (String.concat "," !lvar)
      ^ "), lp;\n"
      ^ "ideal I = "
      ^ (String.concat ",\n" (List.map Dansideal.stringP lpol1)) ^ ";\n"
      ^ "ideal J = groebner(I);\n"
      ^ "J;\n"
      ^ "exit;\n" in
    let _ =
      let ch = open_out inputfgb in
      output_string ch input_text; close_out ch;
	  trace "INPUT GB:";
	  unix ("cat " ^ inputfgb ^ " >>  " ^ gbdir ^ "/log_gb");
      trace "" in
    (* run Singular *)
    let _ =
      let t1 = Unix.gettimeofday() in
      unix (singular_path ^ " -q " ^ inputfgb ^ " 1> " ^ outputfgb ^ " 2>&1");
      let t2 = Unix.gettimeofday() in
      trace ("Execution time of Singular: " ^ string_of_float (t2 -. t1) ^ " seconds");
      trace "OUTPUT GB:";
	  unix ("cat " ^ outputfgb ^ " >>  " ^ gbdir ^ "/log_gb");
      trace "" in
    (* parse the output from Singular *)
    let gb = parse_singular_output outputfgb in
    let _ =
      trace "PARSED GB:";
      trace (string_of_gb lvar gb) in
    gb
  else if !version = MagmaR || !version = MagmaZ
  then
    (* prepare the input to magma *)
    let input_text =
      "R := " ^ (if !version = MagmaR then "RationalField()" else "IntegerRing()") ^ ";\n"
      ^ "S<" ^ (String.concat "," !lvar) ^ "> := PolynomialRing(R, " ^ string_of_int (List.length !lvar) ^ ");\n"
      ^ "I := [\n"
      ^ (String.concat ",\n" (List.map Dansideal.stringP lpol1)) ^ "\n];\n"
      ^ "J := GroebnerBasis(I);\n"
      ^ "J;\n"
      ^ "exit;\n" in
    let _ =
      let ch = open_out inputfgb in
      output_string ch input_text; close_out ch;
	  trace "INPUT GB:";
	  unix ("cat " ^ inputfgb ^ " >>  " ^ gbdir ^ "/log_gb");
      trace "" in
    (* run magma *)
    let _ =
      let t1 = Unix.gettimeofday() in
      unix (magma_path ^ " " ^ inputfgb ^ " 1> " ^ outputfgb ^ " 2>&1");
      let t2 = Unix.gettimeofday() in
      trace ("Execution time of Magma: " ^ string_of_float (t2 -. t1) ^ " seconds");
      trace "OUTPUT GB:";
	  unix ("cat " ^ outputfgb ^ " >>  " ^ gbdir ^ "/log_gb");
      trace "" in
    (* parse the output from magma *)
    let gb = parse_magma_output outputfgb in
    let _ =
      trace "PARSED GB:";
      trace (string_of_gb lvar gb) in
    gb
  else
	(let textinputfgb =
	   if !version = JCF1
	   then
	     "#C ./serveur__DMP__Lexp__GINT -pipe2 -read " ^ inputfgb ^ "\n"
	     ^ "#vars ["^(String.concat "," !lvar)^"]\n"
	     ^ "#properties [System]\n"
	     ^ "#list\n"
	     ^ "["^(String.concat ",\n" (List.map Dansideal.stringP lpol1)) ^ "]\n"
	   else
	     "(" ^ (String.concat "," !lvar) ^ "),"
	     ^ (replace " " ""
		            (String.concat ","
		                           (List.map Dansideal.stringP lpol1)))
	 in
	 unix ("echo \"" ^ textinputfgb ^ "\n\" > " ^ inputfgb);
	 let fgbcom =
	   if !version = JCF1
	   then
	     serveur__DMP__Lexp__GINT_path ^ " -pipe2 -read " ^ inputfgb ^ " >" ^ outputfgb
	   else
	     fgbascii_path ^ " <" ^ inputfgb ^ " 2>" ^ outputfgb in
	 trace "INPUT GB:";
	 unix ("cat " ^ inputfgb ^ " >>  " ^ gbdir ^ "/log_gb");
	 unix fgbcom;
	 trace "OUTPUT GB:";
	 unix ("cat " ^ outputfgb ^ " >>  " ^ gbdir ^ "/log_gb");
	 let contenu = read_string2 outputfgb in
	 trace "Contenu lu";
	 let gb = lire_fgb contenu in
	 trace "Base de grobner lue";
	 (*unix ("rm -f "^inputfgb);
       unix ("rm -f "^outputfgb);*)
	 gb)

let deg_nullstellensatz lpol p =
  (* lpol = p1, ..., pn *)
  let n = List.length lpol in
  let m = (!nvars) in
  (*  t=m+2 ei=-i z=m+1*)
  let (lvar, lpol1) = compute_gb_input lpol p in
  let gb = compute_gb_output lpol lvar lpol1 in
  (* on garde les polynomes de gb avec t de degre 1 dans le monome dominant
     normalement, il ne doit y en avoir qu'un *)
  let q = (List.filter
	         (fun p -> match p with
		                 [] -> false
	                   | (_,mon)::_ -> mon.(1) = 1)
             gb) in
  let q' = List.nth q 0 in
  let lq = ref [] in
  let degz = ref 0 in
  for i = 1 to n + 1 do
    let i0 = n + m + 4 - i in
    (* les monomes qui sont construits a l'aide de ei *)
    let qi = List.filter
	           (fun p ->
	            match p with
                  (_,mon) ->  mon.(i0) > 0
	           )
          q' in
    (* mutiliplier par le coef de e (1 ou -1) dans q' *)
    let qi = List.map
	           (fun p ->
	            match p with
                  (a,mon) ->
		          ((mult_coef a
		                      (opp_coef
		                         (coef_of_int
			                        (signe_coef (fst (List.nth q' 0)))))), mon))
	           qi in
    (* on enleve ei *)
    let qqi = List.map
	            (fun p ->
                 let mon = snd p in
                 let c = fst p in
                 let mon1 = Array.copy mon in
                 mon1.(i0) <- mon.(i0) - 1;
                 (c,mon1))
	            qi in
    (* et on regarde le degre de z *)
    List.iter
	  (fun qi ->
       let deg' = (snd qi).(2) in
       (if (compare deg' !degz) = 1 then
	      degz := deg'))
	  qqi;
    lq := [qqi]@(!lq);
  done;

  let pi = pol_rec_to_sparse p (-n-1) (m+2) in
  lq := List.map
	      (fun hi ->
	       (* z^a devient z^(degz-a) *)
	       let gi = Dansideal.specialsubstP (m+3) hi 2 !degz in
	       (*z devient p*)
	       Dansideal.substP (m+3) gi 2 pi)
	      !lq;

  let lqr = List.map (fun p->pol_sparse_to_rec (-n-1) (m+2) p) !lq in

  let specialcoef = fst (List.nth q' 0) in
  let coefs =
    String.concat ",\n" (List.map string_of_P lqr)
  in
  trace ("degre: " ^ (string_of_int !degz) ^ "\n"
		 ^ "coefficients:\n " ^ coefs);
  trace ("ce polynome doit etre nul:"
	     ^ "(" ^ (string_of_P p) ^ ")^" ^ (string_of_int !degz)
	     ^ "\n-("
	     ^ (String.concat "\n+"
	                      (List.map2
		                     (fun c p -> "(" ^ (string_of_P c) ^ ")*(" ^ (string_of_P p) ^ ")")
		                     (List.tl lqr) lpol))
	     ^ ")");
  (specialcoef, (lqr, !degz))
;;

(* calcul de l'exposant et des coefficients de la combinaison lineaire *)

let comb_lin1 lp =
  nvars:=0;(* mise a jour par term_polyf *)
  let lp0 = List.map term_polyf lp in
  let lp = List.map snd lp0 in
  (* lp = liste de polynomes recursifs *)
  let p::lp1 = List.rev lp in
  let lpol = List.rev lp1 in
(* montrer lp = 0 => p=0 *)
  let (c,(_::lq,d))=  deg_nullstellensatz lpol p in
  let c = abs_ent c in
(* on a
         (-c)*p^d = sum lq*lp
*)
  let lc = (Pint c)::lq in
  (Pow ((poly_term p),d))::(List.map poly_term lc)



(* ------------------------------------------------------------------------- *)
(*  Main entry point                                                         *)
(* ------------------------------------------------------------------------- *)

let coq_lt = 1
let coq_jcf1 = 2
let coq_jcf2 = 3
let coq_singularR = 4
let coq_singularZ = 5
let coq_magmaR = 6
let coq_magmaZ = 7

let convert_coq_version (v : Globnames.global_reference) : version =
  match v with
  | Globnames.ConstructRef ((ind, _), idx) when Names.MutInd.to_string ind = "GBArith.GBCompute.gb_algorithm" ->
     if idx = coq_lt then LT
     else if idx = coq_jcf1 then JCF1
     else if idx = coq_jcf2 then JCF2
     else if idx = coq_singularR then SingularR
     else if idx = coq_singularZ then SingularZ
     else if idx = coq_magmaR then MagmaR
     else if idx = coq_magmaZ then MagmaZ
     else failwith "Unknown algorithm."
  | Globnames.ConstRef cr ->
     begin
     match Global.body_of_constant cr with
     | None -> failwith "Unknown algorithm."
     | Some c ->
        if Constr.equal c (Lazy.force CoqTerm._LT) then LT
        else if Constr.equal c (Lazy.force CoqTerm._JCF1) then JCF1
        else if Constr.equal c (Lazy.force CoqTerm._JCF2) then JCF2
        else if Constr.equal c (Lazy.force CoqTerm._SingularR) then SingularR
        else if Constr.equal c (Lazy.force CoqTerm._SingularZ) then SingularZ
        else if Constr.equal c (Lazy.force CoqTerm._MagmaR) then MagmaR
        else if Constr.equal c (Lazy.force CoqTerm._MagmaZ) then MagmaZ
        else failwith "Unknown algorithm."
     end
  | _ -> failwith "Unknown algorithm."

let is_mac () =
  try
    let ic = Unix.open_process_in "uname" in
    let uname = input_line ic in
    let () = close_in ic in
    uname = "Darwin"
  with _ ->
    false

let gb_compute ?version:ver lp =
  let _ = init_trace () in
  let ver =
    match ver with
    | None -> default_version
    | Some v -> v in
  if ver = JCF1 && not (Sys.file_exists serveur__DMP__Lexp__GINT_path) then
    raise (ToolNotFound serveur__DMP__Lexp__GINT_path)
  else if ver = JCF2 && not (Sys.file_exists fgbascii_path) then
    raise (ToolNotFound fgbascii_path)
  else if is_mac () && (ver = JCF1 || ver = JCF2) then
    raise NotSupportedByMacOS
  else
    let ver_str = string_of_version ver in
    let _ = trace ("Version: " ^ ver_str) in
    let _ = version := ver in
    let lc = comb_lin1 lp in
    lc
