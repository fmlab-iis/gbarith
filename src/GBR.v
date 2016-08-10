(*
                     Tactic gbR
                     L.Pottier, 08-2008

Tactic gbR proves p1?0, ... , pn?0 => p?0
where ? is = or <>, p1,...,pn,p are arithmetic expressions on real numbers.
Example: x^2+2*x*y=0 -> y^2=0 -> x+y=0.

The tactic uses Gröbner bases computations, performed by the programs F4 and GB of JC.Faugere,
and extracted code from L.Thery proof of Buchberger algorithm.

It uses also some code from the sos tactic by L.Théry.

The tactic produces also certificates, that can be inserted using copy/paste
in the proof in place of the tactic. Then the proof is independent of the external
programs that computed Grobner bases (suggestion of J.Narboux).

The main tactic is gbR.

Tactics that uses a specific algorithm:
- gbR_choice 3: for F4 algorithm
- gbR_choice 2: for GB algorithm
- gbR_choice 1: for L.Thery certified algorithm

Example (see more examples in gbtest.v):

Goal forall x y z:R, x^2+x*y=0 -> y^2+x*y=0 -> x+y=0.
gbR.
Qed.

Same proof, using certificate printed during the previous proof:

Goal forall x y z:R, x^2+x*y=0 -> y^2+x*y=0 -> x+y=0.
 intros; check_gbR

(hd 0
   (rev
      (interpret_list
         (lceq (Add (Pow (Var 2) 2) (Mul (Var 2) (Var 1)))
            (lceq (Add (Pow (Var 1) 2) (Mul (Var 2) (Var 1)))
               (lceq (Sub (Add (Var 2) (Var 1)) (Const 0 1)) lnil)))
         (y :: x :: nil))))

(rev
   (tail
      (rev
         (interpret_list
            (lceq (Add (Pow (Var 2) 2) (Mul (Var 2) (Var 1)))
               (lceq (Add (Pow (Var 1) 2) (Mul (Var 2) (Var 1)))
                  (lceq (Sub (Add (Var 2) (Var 1)) (Const 0 1)) lnil)))
            (y :: x :: nil)))))
 (y :: x :: nil)

(lceq
   (Pow
      (Add
         (Add Zero
            (Mul
               (Add (Add Zero (Mul (Const 0 1) (Const 1 1)))
                  (Mul (Const 1 1) (Pow (Var 1) 1))) (Const 1 1)))
         (Mul (Const 1 1) (Pow (Var 2) 1))) 2)
   (lceq (Const 1 1) (lceq (Const 1 1) (lceq (Const 1 1) lnil))))
 .
Qed.

*)


From Coq Require Import ZArith.
From Coq Require Import Znumtheory.
From Coq Require Export Reals.
From Coq Require Import List.
From GBArith Require Export GBCompute.


Open Scope R_scope.

(********************************************)
(* Convert positive into R                  *)
(********************************************)

Fixpoint IPR p {struct p}: R :=
  match p with
    xH => 1
  | xO xH => 1 + 1
  | xO p1 => 2 * (IPR p1)
  | xI xH => 1 + (1 + 1)
  | xI p1 => 1 + 2 * (IPR p1)
  end.

Definition IZR1 z :=
  match z with
    Z0 => 0
  | Zpos p => IPR p
  | Zneg p => -(IPR p)
  end.


(********************************************)
(* Test for constant in R                   *)
(********************************************)

Ltac NCst t :=
  match t with
  | O => constr:(1%positive)
  | S O => constr:(1%positive)
  | S ?t1 =>
    match (NCst t1) with
    | false => constr:false
    | ?x1 => let x2 := eval compute in (Psucc x1) in
             x2
    end
  | _ => constr:false
  end.

(********************************************)
(* Belonging in a list for R                *)
(********************************************)

Ltac rIN a l :=
  match l with
  | (cons a ?l) => constr:true
  | (cons _ ?l) => rIN a l
  | _ => constr:false
  end.

(********************************************)
(* Adding a variable in a list for R        *)
(********************************************)

Ltac rAddFv a l :=
  match (rIN a l) with
  | true => constr:l
  | _ => constr:(cons a l)
  end.

(********************************************)
(* Adding a variable in a list for R        *)
(********************************************)

Ltac rFind_at a l :=
  match l with
  | (cons a _) => constr:xH
  | (cons _ ?l) => let p := rFind_at a l in
                   let v := constr:(Psucc p) in
                   let v1 := eval compute in v in
                   v1
  | _ => constr:xH
  end.

(********************************************)
(* Computing the list of variables for R    *)
(********************************************)

Ltac variables t :=
  let rec aux t fv :=
      match t with
      | 0 => fv
      | 1 => fv
      | False  => fv
      | ?t1 -> ?g1 =>
        let fv1  := aux t1 fv in
        let fv2  := aux g1 fv1 in constr:fv2
      | (_ <= ?t1) => aux t1 fv
      | (_ < ?t1) => aux t1 fv
      | (?t1 = _) => aux t1 fv
      | (?t1 + ?t2) =>
        let fv1  := aux t1 fv in
        let fv2  := aux t2 fv1 in constr:fv2
      | (?t1 * ?t2) =>
        let fv1  := aux t1 fv in
        let fv2  := aux t2 fv1 in constr:fv2
      | (?t1 - ?t2) =>
        let fv1  := aux t1 fv in
        let fv2  := aux t2 fv1 in constr:fv2
      | (-?t1) =>
        let fv1  := aux t1 fv in fv1
      | (?t1 ^ ?t2) =>
        let fv1  := aux t1 fv in
        match NCst t2 with
        | false => let fv1 := rAddFv t fv in constr:fv1
        | _ => fv1
        end
      | _ => let fv1 := rAddFv t fv in constr:fv1
      end
  in aux t (@nil R).

(********************************************)
(* Syntaxification tactic for R             *)
(********************************************)

Ltac abstrait t fv :=
  let rec aux t :=
      match t with
      | 0 => constr:(Const 0 1)
      | 1 => constr:(Const 1 1)
      | 2 => constr:(Const 2 1)
      | (?t1 = 0) -> ?g1 =>
        let v1  := aux t1 in
        let v2  := aux g1 in constr: (lceq v1 v2)
      | (?t1 = 0) =>
        let v1  := aux t1 in constr: (lceq v1 lnil)
      | (?t1 + ?t2) =>
        let v1  := aux t1 in
        let v2  := aux t2 in constr:(Add v1 v2)
      | (?t1 * ?t2) =>
        let v1  := aux t1 in
        let v2  := aux t2 in constr:(Mul v1 v2)
      | (?t1 - ?t2) =>
        let v1  := aux t1 in
        let v2  := aux t2 in constr:(Sub v1 v2)
      | (?t1 ^ 0) =>
        constr:(Const 1 1)
      | (?t1 ^ ?n) =>
        match NCst n with
        | false => let p := rFind_at t fv in constr:(Var p)
        | ?n1 => let v1  := aux t1 in constr:(Pow v1 n1)
        end
      | (- ?t1) =>
        let v1  := aux t1 in constr:(Opp v1)
      |  False  => constr:lnil
      | _ =>
        let p := rFind_at t fv in constr:(Var p)
      end
  in aux t.

(********************************************)
(* Unsyntaxification for R                  *)
(********************************************)

Fixpoint interpret t fv {struct t}: R :=
  match t with
  | (Add t1 t2) =>
    let v1 := interpret t1 fv in
    let v2 := interpret t2 fv in (v1 + v2)
  | (Mul t1 t2) =>
    let v1 := interpret t1 fv in
    let v2 := interpret t2 fv in (v1 * v2)
  | (Sub t1 t2) =>
    let v1 := interpret t1 fv in
    let v2 := interpret t2 fv in (v1 - v2)
  | (Opp t1) =>
    let v1 := interpret t1 fv in (-v1)
  | (Pow t1 t2) =>
    let v1 := interpret t1 fv in v1 ^ (nat_of_P t2)
  | (Const t1 t2) => (IZR1 t1)
  | (Var n) => nth (pred (nat_of_P n)) fv 0
  | Zero => 0
  end.

Fixpoint interpret_list l fv {struct l}:list R :=
  match l with
  | lnil => nil
  | lceq t l1 => (interpret t fv)::(interpret_list l1 fv)
  end.

Fixpoint combine l1 l2 {struct l1}:R :=
  match l1 with
  | nil => 0
  | a::l11 =>
    match l2 with
    | nil => 0
    | b::l21 => a * b + (combine l11 l21)
    end
  end.

Lemma psos_r1b : forall x y, x - y = 0 -> x = y.
Proof.
  exact Rminus_diag_uniq.
Qed.

Lemma psos_r1 : forall x y, x = y -> x - y = 0.
Proof.
  exact Rminus_diag_eq.
Qed.

Ltac equalities_to_goal :=
  match goal with
  |  H: (@eq R ?x 0) |- _ =>
     try generalize H; clear H
  |  H: (@eq R 0 ?x) |- _ =>
     try generalize (sym_equal H); clear H
  |  H: (@eq R ?x ?y) |- _ =>
     try generalize (psos_r1 _ _ H); clear H
  end.

Lemma gbR_l2 : forall p : R, forall n : nat, p ^ n = 0 -> p = 0.
Proof.
  intro p.
  intro n.
  intro npos.
  induction n.
  simpl in npos.
  absurd (1=0); auto with *.
  simpl in npos.
  elim (Rmult_integral _ _ npos); intros.
  auto.
  auto.
Qed.

Lemma gbR_l1 : forall c p : R, forall n : nat, ~ c = 0 -> c * p ^ n = 0 -> p = 0.
Proof.
  intros.
  elim (Rmult_integral _ _ H0); intros.
  absurd (c=0); auto.
  apply gbR_l2 with n; auto.
Qed.

Ltac rewrite_with_goal H:=
  match goal with
  | |- (?x = R0) -> ?g =>
    let Hgb0:=fresh "Hgb" in intro Hgb0;
      try rewrite Hgb0 in H; try rewrite Hgb0
  end.

Ltac rewrite_with_goal_in_goal:=
  match goal with
  | |- (?x = R0) -> ?g =>
    let Hgb0:=fresh "Hgb" in intro Hgb0;
      try rewrite Hgb0
  end.

Ltac equalities_to_goal2:=
  match goal with
  |  H: (@eq R ?x 0) |- _ =>
     try generalize H; clear H
  end.

Lemma gbR_not1: forall x y:R, (not (x=y))-> exists z:R, z*(x-y)-1=0.
Proof.
  intros.
  exists (1/(x-y)).
  field.
  unfold not.
  unfold not in H.
  intros.
  apply H.
  replace x with ((x-y)+y).
  rewrite H0.
  ring.
  ring.
Qed.

Lemma gbR_not1_0: forall x:R, (not (x=0))-> exists z:R, z*x-1=0.
Proof.
  intros.
  exists (1/(x)).
  field.
  auto.
Qed.

Lemma gbR_not2: not (1=0).
Proof.
  auto with *.
Qed.

Lemma gbR_diff: forall x y:R, x<>y -> x-y<>0.
Proof.
  intros x y Hne Heq.
  apply Hne.
  apply Rminus_diag_uniq.
  exact Heq.
Qed.

(* Removes x<>0 from hypothesis *)
Ltac gbR_not_hyp:=
  match goal with
  | H : ?x <> ?y |- _ =>
     match y with
     | 0 =>
      let H1 := fresh "Hgb" in
      let y := fresh "x" in
      generalize (@gbR_not1_0 _ H); clear H; intro H1; elim H1; clear H1; intros y H1
     | _ => generalize (@gbR_diff _ _ H); clear H; intro
     end
  end.

Ltac gbR_not_goal :=
  match goal with
  | |- ?x <> ?y =>
    unfold not; intro; apply gbR_not2
  | |- False => apply gbR_not2
  end.

Ltac gbR_begin :=
  intros;
  repeat gbR_not_hyp;
  try gbR_not_goal;
  try apply psos_r1b;
  repeat equalities_to_goal.

Ltac gbR_end p lp l t :=
  match t with
  | lceq (Pow ?p0 ?d)  (lceq ?c ?lc) =>
    let lc := constr:(interpret_list lc l) in
    let p0 := constr:(interpret p0 l) in
    let c := constr:(interpret c l) in
    let e := constr:(combine lc lp) in
    let Hgb1 := fresh "Hgb" in
    let Hgb2 := fresh "Hgb" in
    cut (p=p0);
      [simpl;intro Hgb1;rewrite Hgb1;
       cut (c*p0^(nat_of_P d)=e);
       [simpl;idtac
       |simpl; try ring]
      |simpl;try ring];
      intro Hgb2; intros;
      apply gbR_l1 with c (nat_of_P d);
      [try(simpl; discrR)
      |try(simpl; rewrite Hgb2 ; repeat equalities_to_goal2;
           repeat rewrite_with_goal_in_goal;ring)]
  | lceq (Const ?p0 ?d)  (lceq ?c ?lc) => (* d=0 *)
    let lc := constr:(interpret_list lc l) in
    let c := constr:(interpret c l) in
    let e := constr:(combine lc lp) in
    let Hgb1:=fresh "Hgb" in
    cut (c=e);
      [simpl; intro Hgb1 ;repeat rewrite_with_goal Hgb1;
       ring_simplify in Hgb1;
       match goal with
       | H : ?x = 0 |- _ => absurd (x=0);[discrR|trivial] end
      |simpl;try ring]
  end.

(** This tactic is slightly changed by Ming-Hsien Tsai to use the ML plugin. *)
Ltac gbR_nullstellensatz t program k :=
  let l := variables t in
  let a := abstrait t l in
  let lp1 := constr:(List.rev (interpret_list a l))  in
  let p := constr:(List.hd 0 lp1) in
  let lp := constr:(List.rev (List.tail lp1)) in
  gbarith_compute program a ltac:(fun t =>
    let res := constr:(p, lp, l, t) in
    k res
  ).

(** This tactic is slightly changed by Ming-Hsien Tsai to use the ML plugin. *)
Ltac gbR_choice program :=
  match program with
   | LT => idtac "(* with L.Thery algorithm, proved in Coq *)"
   | JCF1 => idtac "(* with JC.Faugere algorithm GB *)"
   | JCF2 => idtac "(* with JC.Faugere algorithm F4 *)"
  end;
  gbR_begin;
  match goal with
   |- ?t =>
   gbR_nullstellensatz t program ltac:(fun res =>
     match res with
       (?p, ?lp, ?l, ?t) =>
       let p1 := eval simpl in p in
       let lp1 := eval simpl in lp in
       let l1 := eval simpl in l in
       let t1 := eval simpl in t in
       idtac "p ="; idtac p1;
       idtac "lp = "; idtac lp1;
       idtac "l = "; idtac l1;
       idtac "t = "; idtac t1; idtac ".";
  	   gbR_end p lp l t
     end
   )
end.

Ltac check_gbR p lp l t := gbR_end p lp l t.

Ltac gbR := gbR_choice JCF1 || gbR_choice JCF2 || gbR_choice LT.
