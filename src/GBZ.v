
(** This file is copied from gb-keappa by Loïc Pottier except that
 *  - admitted lemmas are proved,
 *  - Z.pow_pos and Zpower_nat are supported, and
 *  - IZR is converted to IZR1 such that IZR n can be computed more quickly
 *    when n is a large constant.
 *)

From Coq Require Export ZArith.
From Coq Require Import Zpow_facts.
From Coq Require Import Wf_Z.
From Coq Require Import Znumtheory.
From Coq Require Import List.
From GBArith Require Export GBR.


Open Scope Z_scope.

(** Added by Ming-Hsien Tsai to prove IZR n = IZR1 n *)

Lemma xO_mul2 (n : positive) :
  (n~0)%positive = (2 * n)%positive.
Proof.
  reflexivity.
Qed.

Lemma xI_mul2_add1 (n : positive) :
  (n~1)%positive = (2 * n + 1)%positive.
Proof.
  reflexivity.
Qed.

Lemma pos_lt_well_founded :
  well_founded Pos.lt.
Proof.
  intro n.
  apply Pos.peano_ind.
  - apply Acc_intro; intros m Hm.
    apply False_ind; exact (Pos.nlt_1_r m Hm).
  - intros m Hm.
    apply Acc_intro; intros x Hx.
    generalize (Pos.lt_succ_r x m); intros [H1 H2].
    generalize (H1 Hx); clear Hx H1 H2; intro Hx.
    generalize (Pos.lt_eq_cases x m); intros [H1 H2].
    generalize (H1 Hx); clear Hx H1 H2; intro Hx.
    elim Hx; clear Hx; intro Hx.
    + apply Hm; assumption.
    + rewrite Hx; assumption.
Qed.

Lemma pos_1_lt_xI n : (1 < n~1)%positive.
Proof.
  reflexivity.
Qed.

Lemma pos_lt_xO n : (n < n~0)%positive.
Proof.
  rewrite xO_mul2.
  generalize (Pos.mul_lt_mono_r n 1 2); intros [H1 H2].
  apply H1; clear H1 H2.
  reflexivity.
Qed.

Lemma pos_lt_xI n : (n < n~1)%positive.
Proof.
  rewrite xI_mul2_add1.
  generalize (Pos.lt_succ_r n (2 * n)); intros [H1 H2].
  apply H2; clear H1 H2.
  generalize (Pos.mul_le_mono_r n 1 2); intros [H1 H2].
  apply H1; clear H1 H2.
  intro H; discriminate.
Qed.

Lemma IPR_INR :
  forall n : positive,
    IPR n = INR (Pos.to_nat n).
Proof.
  apply (well_founded_ind pos_lt_well_founded (fun n => IPR n = INR (Pos.to_nat n))).
  intros n; elim n; clear n.
  - intro n; destruct n.
    + intros _ IH.
      unfold IPR; fold (IPR n~1).
      rewrite (IH (n~1)%positive (pos_lt_xI (n~1))).
      rewrite (Pos2Nat.inj_xI (n~1)).
      rewrite S_INR.
      rewrite mult_INR.
      rewrite Rplus_comm.
      reflexivity.
    + intros _ IH.
      unfold IPR; fold (IPR n~0).
      rewrite (IH (n~0)%positive (pos_lt_xI (n~0))).
      rewrite (Pos2Nat.inj_xI (n~0)).
      rewrite S_INR.
      rewrite mult_INR.
      rewrite Rplus_comm.
      reflexivity.
    + intros _ _; simpl.
      rewrite Rplus_comm.
      reflexivity.
  - intro n; destruct n.
    + intros _ IH.
      unfold IPR; fold (IPR n~1).
      rewrite (IH (n~1)%positive (pos_lt_xO (n~1))).
      rewrite (Pos2Nat.inj_xO (n~1)).
      rewrite mult_INR.
      reflexivity.
    + intros _ IH.
      unfold IPR; fold (IPR n~0).
      rewrite (IH (n~0)%positive (pos_lt_xO (n~0))).
      rewrite (Pos2Nat.inj_xO (n~0)).
      rewrite mult_INR.
      reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma IPR_add n m :
  IPR (n + m) = (IPR n + IPR m)%R.
Proof.
  rewrite (IPR_INR (n + m)).
  rewrite (IPR_INR n).
  rewrite (IPR_INR m).
  rewrite Pos2Nat.inj_add.
  rewrite plus_INR.
  reflexivity.
Qed.

Lemma IPR_mul n m :
  IPR (n * m) = (IPR n * IPR m)%R.
Proof.
  rewrite (IPR_INR (n * m)).
  rewrite (IPR_INR n).
  rewrite (IPR_INR m).
  rewrite Pos2Nat.inj_mul.
  rewrite mult_INR.
  reflexivity.
Qed.

Lemma IZR_IZR1 : forall n, IZR n = IZR1 n.
Proof.
  intro n; destruct n.
  - reflexivity.
  - unfold IZR; unfold IZR1.
    rewrite IPR_INR.
    reflexivity.
  - unfold IZR; unfold IZR1.
    rewrite IPR_INR.
    reflexivity.
Qed.

Ltac IZR_to_IZR1 :=
  repeat (rewrite IZR_IZR1 in *).

Ltac IZR1_to_IZR :=
  repeat (rewrite <- IZR_IZR1 in *).

(***)

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
Lemma IZR_pow_pos n p :
  IZR (Z.pow_pos n p) = (IZR n ^ (Pos.to_nat p))%R.
Proof.
  rewrite Zpower_pos_nat;
  rewrite Zpower_nat_Z;
  rewrite <- RIneq.pow_IZR.
  reflexivity.
Qed.
Lemma IZR_power_nat n p :
  IZR (Zpower_nat n p) = (IZR n ^ p)%R.
Proof.
  rewrite Zpower_nat_Z;
  rewrite <- RIneq.pow_IZR.
  reflexivity.
Qed.
Ltac gbZversR2:=
  repeat
  (rewrite gbZR1 in * ||
   rewrite gbZR2 in * ||
   rewrite gbZR3 in * ||
   rewrite gbZR4 in * ||
   rewrite IZR_pow_pos in * ||
   rewrite IZR_power_nat in * ||
   rewrite <- RIneq.pow_IZR in *).

Ltac gbZ_begin :=
 intros;
 gbZversR1;
 gbZversR2;
 IZR_to_IZR1;
 simpl in *.
 (*cbv beta iota zeta delta [nat_of_P Pmult_nat plus mult] in *.*)

Ltac gbZ :=
 gbZ_begin; gbR.
