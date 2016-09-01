
From Coq Require Import ZArith.

Inductive term : Set :=
| Zero : term
| Const : Z -> positive -> term
| Var : positive -> term
| Opp : term -> term
| Add : term -> term -> term
| Sub : term -> term -> term
| Mul : term -> term -> term
| Pow : term -> positive -> term.

Inductive lineq : Set :=
  lnil : lineq
| lceq : term -> lineq -> lineq.

Declare ML Module "gbarith_plugin".

Inductive gb_algorithm : Set :=
| LT
| JCF1
| JCF2
| SingularR
| SingularZ.

Definition default_gb_algorithm := JCF1.

Ltac gbarith_compute v t k :=
  let id := fresh in
  gbarith_compute_ml v id t;
  let res := eval compute in id in
  k res.

Ltac default_gbarith_compute t k :=
  gbarith_compute default_gb_algorithm t k.
