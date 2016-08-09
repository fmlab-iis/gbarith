
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

type version =
  | LT   (* Laurent Théry *)
  | JCF1 (* Jean-Charles Faugere *)
  | JCF2 (* Jean-Charles Faugere *)

val cterm_of_oterm : term -> Constr.t

val oterm_of_cterm : Constr.t -> term

val clineq_of_olineq : lineq -> Constr.t

val olineq_of_clineq : Constr.t -> lineq

val gb_compute : ?version:version -> lineq -> lineq
