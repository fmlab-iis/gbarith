
(** This file is copied from gb-keappa by Loïc Pottier except that
 *  - admitted lemmas are proved, and
 *  - gbZ is slightly modified.
 *)

From Coq Require Export ZArith.
From Coq Require Import Zpow_facts.
From Coq Require Import Wf_Z.
From Coq Require Import Znumtheory.
From Coq Require Import List.
From GBArith Require Export GBR.


Open Scope Z_scope.

Lemma gbZhypR: forall x y : Z, x = y -> (IZR x) = (IZR y).
Proof.
  intros x y Hxy.
  rewrite Hxy.
  reflexivity.
Qed.

Lemma gbZconclR: forall x y : Z, (IZR x) = (IZR y) -> x = y.
Proof.
  exact eq_IZR.
Qed.

Lemma gbZhypnotR: forall x y : Z, x <> y -> (IZR x) <> (IZR y).
Proof.
  intros x y Hne Heq; apply Hne; exact (gbZconclR x y Heq).
Qed.

Lemma gbZconclnotR: forall x y:Z, (IZR x) <> (IZR y) -> x <> y.
Proof.
  intros x y Hne Heq; apply Hne; exact (gbZhypR x y Heq).
Qed.

Ltac gbZversR1 :=
 repeat
  (match goal with
   | H:(@eq Z ?x ?y) |- _ => generalize (@gbZhypR _ _ H); clear H; intro H
   | |- (@eq Z ?x ?y) => apply gbZconclR
   | H:not (@eq Z ?x ?y) |- _ => generalize (@gbZhypnotR _ _ H); clear H; intro H
   | |- not (@eq Z ?x ?y) => apply gbZconclnotR
   end).

Lemma gbZR1: forall x y:Z, IZR(x+y) = (IZR(x)+IZR(y))%R.
Proof.
  exact plus_IZR.
Qed.
Lemma gbZR2: forall x y:Z, IZR(x*y) = (IZR(x)*IZR(y))%R.
Proof.
  exact mult_IZR.
Qed.
Lemma gbZR3: forall x y:Z, IZR(x-y) = (IZR(x)-IZR(y))%R.
Proof.
  exact minus_IZR.
Qed.
Lemma gbZR4: forall x:Z, forall p:positive, IZR(x^(Zpos p)) = (IZR(x)^(nat_of_P p))%R.
Proof.
  intros x p.
  generalize (pow_IZR x (Pos.to_nat p)); intro H.
  rewrite H.
  rewrite positive_nat_Z.
  reflexivity.
Qed.
Ltac gbZversR2:=
  repeat
  (rewrite gbZR1 in * ||
   rewrite gbZR2 in * ||
   rewrite gbZR3 in * ||
   rewrite gbZR4 in *).

Ltac gbZ_begin :=
 intros;
 gbZversR1;
 gbZversR2;
 simpl in *.
 (*cbv beta iota zeta delta [nat_of_P Pmult_nat plus mult] in *.*)

Ltac gbZ :=
 gbZ_begin; gbR.
