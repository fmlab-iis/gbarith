
(*i camlp4deps: "parsing/grammar.cma" i*)

open Gbarith_compute

open Ltac_plugin
open Stdarg

DECLARE PLUGIN "gbarith_plugin"

let gbarith_compute ver id lp =
  Proofview.Goal.enter (fun gl ->
    try
      let olp = (olineq_of_clineq lp) in
      let over = convert_coq_version ver in
      let olc = gb_compute ~version:over olp in
      let lc = clineq_of_olineq olc in
      Tactics.letin_tac None (Names.Name id) (EConstr.of_constr lc) None Locusops.nowhere
    with ToolNotFound t ->
      Proofview.V82.tactic (Tacticals.tclFAIL 0 (Pp.str ("the tool " ^ t ^ " is not found")))
    | NotSupportedByMacOS ->
      Proofview.V82.tactic (Tacticals.tclFAIL 0 (Pp.str "not supported by Mac OS"))
  )
TACTIC EXTEND mypos
| ["gbarith_compute_ml" reference(ver) ident(id) constr(lp)] -> [gbarith_compute ver id (EConstr.Unsafe.to_constr lp)]
END
