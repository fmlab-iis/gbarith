
(*i camlp4deps: "parsing/grammar.cma" i*)

open Gbarith_compute

open Num

open Globnames
open Glob_term
open Proofview.Notations
open Tacexpr
open Tacinterp

DECLARE PLUGIN "gbarith_plugin"

let gbarith_compute ver id lp =
  Proofview.Goal.enter (fun gl ->
    let version =
      if ver = 0 then LT
      else if ver = 1 then JCF1
      else JCF2 in
    let lc = clineq_of_olineq (gb_compute ~version:version (olineq_of_clineq lp)) in
    Tactics.letin_tac None (Names.Name id) lc None Locusops.nowhere
  )
TACTIC EXTEND mypos
| ["gbarith_compute" integer(ver) ident(id) constr(lp)] -> [gbarith_compute ver id lp]
END
