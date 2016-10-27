
(** This file is copied from gb-keappa by Loïc Pottier except that
 *  - proofs of some lemmas are simplified, and
 *  - gb_exists is rewritten.
 *)

(********************************************************************************)
(*   Preuves d'arithmetique (papier d'Harrison, CADE 2007) *)
(********************************************************************************)

From Coq Require Export ZArith.
From Coq Require Import Zpow_facts.
From Coq Require Import Wf_Z.
From Coq Require Import Znumtheory.
From Coq Require Import List.
From GBArith Require Export GBCompute.
Open Scope Z_scope.

(********************************************)
(* Test for positive constant in Z          *)
(********************************************)

Ltac NCst t :=
  match t with
  | O => constr:(1%positive)
  | Zpos ?t1 => t1
  | _ => constr:false
  end.

(********************************************)
(* Belonging in a list for Z                *)
(********************************************)

Ltac rIN a l :=
  match l with
  | (cons a ?l) => constr:true
  | (cons _ ?l) => rIN a l
  | _ => constr:false
  end.

(********************************************)
(* Adding a variable in a list for Z        *)
(********************************************)

Ltac rAddFv a l :=
  match (rIN a l) with
  | true => constr:l
  | _ => constr:(cons a l)
  end.

(********************************************)
(* Adding a variable in a list for Z        *)
(********************************************)

Ltac rFind_at a l :=
  match l with
  | (cons a _) => constr:xH
  | (cons _ ?l) =>
    let p := rFind_at a l in
    let v := constr:(Psucc p) in
    let v1 := eval compute in v in
    v1
  | _ => constr:xH
 end.

(********************************************)
(* Computing the list of variables for Z    *)
(********************************************)

Ltac variables t :=
  let rec aux t fv :=
  match t with
  | 0 => fv
  | 1 => fv
  | Zpos _ => fv
  | Zneg _ => fv
  | False  => fv
  | ?t1 -> ?g1 =>
    let fv1  := aux t1 fv in
    let fv2  := aux g1 fv1 in constr: fv2
  | (_ <= ?t1) => aux t1 fv
  | (_ < ?t1) => aux t1 fv
  | (?t1 = _) => aux t1 fv
  | (?t1 + ?t2) =>
    let fv1  := aux t1 fv in
    let fv2  := aux t2 fv1 in constr: fv2
  | (?t1 * ?t2) =>
    let fv1  := aux t1 fv in
    let fv2  := aux t2 fv1 in constr: fv2
  | (?t1 - ?t2) =>
    let fv1  := aux t1 fv in
    let fv2  := aux t2 fv1 in constr: fv2
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
  in aux t (@nil Z).

(********************************************)
(* Syntaxification tactic for Z             *)
(********************************************)

Ltac abstrait t fv :=
  let rec aux t :=
  match t with
  | 0 => constr:(Const 0 1)
  | 1 => constr:(Const 1 1)
  | 2 => constr:(Const 2 1)
  | Zpos _ => constr:(Const t 1)
  | Zneg _ => constr:(Const t 1)
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
(* Unsyntaxification for Z                  *)
(********************************************)

Fixpoint interpret t fv {struct t}: Z :=
  match t with
  | (Add t1 t2) =>
    let v1  := interpret t1 fv in
    let v2  := interpret t2 fv in (v1 + v2)
  | (Mul t1 t2) =>
    let v1  := interpret t1 fv in
    let v2  := interpret t2 fv in (v1 * v2)
  | (Sub t1 t2) =>
    let v1  := interpret t1 fv in
    let v2  := interpret t2 fv in (v1 - v2)
  | (Opp t1) =>
    let v1  := interpret t1 fv in (-v1)
  | (Pow t1 t2) =>
    let v1  := interpret t1 fv in v1 ^(Zpos t2)
  | (Const t1 t2) =>  t1
  | (Var n) => nth (pred (nat_of_P n)) fv 0
  | Zero => 0
  end.

Fixpoint interpret_list l fv {struct l}:list Z :=
  match l with
  | lnil => nil
  | lceq t l1 => (interpret t fv)::(interpret_list l1 fv)
  end.

Fixpoint combine l1 l2 {struct l1}:Z :=
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
  exact Zminus_eq.
Qed.

Lemma psos_r1 : forall x y, x = y -> x - y = 0.
Proof.
  exact Zeq_minus.
Qed.

Ltac equalities_to_goal :=
  match goal with
  |  H: (@eq Z ?x 0) |- _ =>
     try generalize H; clear H
  |  H: (@eq Z 0 ?x) |- _ =>
     try generalize (sym_equal H); clear H
  |  H: (@eq Z ?x ?y) |- _ =>
     try generalize (psos_r1 _ _ H); clear H
  end.

Lemma gb_l2 : forall p n : Z, n >= 0 -> p^n = 0 -> p = 0.
Proof.
  intro p.
  intro n.
  intro npos.
  apply (natlike_rec2 (fun n : Z => n >= 0 -> p ^ n = 0 -> p = 0)); intros.
  - simpl in H0.
    inversion H0.
  - rewrite Zpower_Zsucc in H2.
    + elim (Zmult_integral _ _ H2); intros.
      * auto.
      * auto with zarith.
    + auto with zarith.
  - auto with zarith.
  - auto with zarith.
Qed.

Lemma gb_l1 :
  forall c p : Z, forall n : Z,
      ~ c = 0 -> n >= 0 -> c * p ^ n = 0 -> p = 0.
Proof.
  intros.
  elim (Zmult_integral _ _ H1); intros.
  absurd (c=0); auto.
  apply gb_l2 with n; auto.
Qed.

Ltac rewrite_with_goal H :=
  match goal with
  | |- (?x = 0) -> ?g =>
    let Hgb0 := fresh "Hgb" in
    intro Hgb0; try rewrite Hgb0 in H; try rewrite Hgb0
  end.

Ltac rewrite_with_goal_in_goal :=
  match goal with
  | |- (?x = 0) -> ?g =>
    let Hgb0:=fresh "Hgb" in
    intro Hgb0; try rewrite Hgb0
  end.

Ltac equalities_to_goal2 :=
  match goal with
  |  H: (@eq Z ?x 0) |- _ =>
     try generalize H; clear H
  |  H: (@eq Z ?x ?y) |- _ =>
     try generalize (@psos_r1 _ _ H); clear H
  end.

Lemma gb_not2 : not (1 = 0).
Proof.
  auto with zarith.
Qed.

Ltac gb_not_goal :=
  match goal with
  | |- ?x <> ?y =>
    unfold not; intro; apply gb_not2
  | |- False => apply gb_not2
  end.

Ltac gbZ_begin :=
  intros;
  try gb_not_goal;
  try apply psos_r1b;
  repeat equalities_to_goal.

Ltac simplZ2 :=
   cbv beta iota zeta delta -[Zmult Zplus Zpower Z.pow_pos Zminus Zopp Zdiv Zmod].

Lemma gbsimplZ1 : forall x : Z, x ^ 1 = x.
Proof.
  exact Z.pow_1_r.
Qed.

Lemma gbsimplZ2 : forall x : Z, 0 * x = 0.
Proof.
  exact Z.mul_0_l.
Qed.

Lemma gbsimplZ3 : forall x : Z, x * 0 = 0.
Proof.
  exact Z.mul_0_r.
Qed.

Lemma gbsimplZ4 : forall x : Z, 1 * x = x.
Proof.
  exact Z.mul_1_l.
Qed.

Lemma gbsimplZ5 : forall x : Z, 0 + x = x.
Proof.
  exact Z.add_0_l.
Qed.

Lemma gbsimplZ6 : forall x : Z, x * 1 = x.
Proof.
  exact Z.mul_1_r.
Qed.

Lemma gbsimplZ7 : forall x : Z, (-1) * x = - x.
Proof.
  intros; ring.
Qed.

Lemma gbsimplZ8 n p :
  Z.pow_pos n p = n ^ (Zpos p).
Proof.
  rewrite Zpower_pos_nat.
  rewrite Zpower_nat_Z.
  rewrite positive_nat_Z.
  reflexivity.
Qed.

Lemma gbsimplZ9 n p :
  Zpower_nat n p = n ^ (Z.of_nat p).
Proof.
  rewrite Zpower_nat_Z.
  reflexivity.
Qed.

Ltac simplZ3 :=
  repeat (rewrite gbsimplZ1 || rewrite gbsimplZ2 || rewrite gbsimplZ3
          || rewrite gbsimplZ4 || rewrite gbsimplZ5 || rewrite gbsimplZ6
          || rewrite gbsimplZ7 || rewrite gbsimplZ8 || rewrite gbsimplZ9).

Ltac simplZ := simplZ2; simplZ3.

Ltac remove_exists_hyp :=
  match goal with
  | H : exists x : Z, _ |- _ =>
    let x := fresh "x" in
    elim H; clear H; intros x H
  end.

Ltac gb_begin2 :=
  intros;
  try apply psos_r1b;
  try repeat equalities_to_goal2.

Ltac lhyps x :=
  match x with
  | ?a -> ?b -> ?c =>
    let d := constr:(b -> c) in
    let lb := lhyps d in constr:(a::lb)
  | ?a -> ?b => constr:(a::nil)
  | ?a => constr:(@nil Prop)
  end.

Ltac ajoute_hyps lh t :=
  match lh with
   | ?a :: ?lh1 => let b := ajoute_hyps lh1 t in constr:(a -> b)
   | _ => t
  end.

Lemma gb_ex_ex1 :
  forall a b : Z,
    (exists x : Z, a = b * x) -> (exists x : Z, a = x * b).
Proof.
  intros.
  destruct H.
  exists x; rewrite H; ring.
Qed.

Lemma gb_ex_ex2 :
  forall a b d x y : Z,
    (exists x : Z, exists y : Z, a = x * b + y * d)  ->
    exists x : Z, exists y : Z, a = b * x + d * y.
Proof.
  intros.
  destruct H.
  destruct H.
  exists x0; exists x1; rewrite H; ring.
Qed.

(* for debugging, to be deleted *)
Ltac print_goal :=
  match goal with
    | |- ?x => idtac x
  end.
Ltac print_left :=
  match goal with
    | |- ?x = ?y => idtac x
  end.
Ltac print_exp e :=
  cut (e = e);
  [ let H := fresh "H" in intro H; clear H |
    simplZ; print_left; reflexivity ].

Ltac gb_exists_original program :=
  intros;
  repeat remove_exists_hyp;
  match goal with
  | |- exists x : Z, ?a = x * ?b => apply gb_ex_ex1; gb_exists_original program
  | |- exists x : Z, ?a = ?b * x =>
    repeat equalities_to_goal2;
    match goal with
    | |- ?g =>
      let lh := lhyps g in
      let t1:= constr:(a = 0) in
      let t := ajoute_hyps lh t1 in
      let t := constr:(b = 0 -> t) in
      let l := variables t in
      let a := abstrait t l in
      let lp1 := constr:(List.rev (interpret_list a l))  in
      let p := constr:(List.hd 0 lp1) in
      let lp := constr:(List.rev (List.tail lp1)) in
      gbarith_compute program a ltac:(fun t =>
        idtac "variables := "; idtac l;
        idtac "a := "; idtac a;
        idtac "lp1 := "; print_exp lp1;
        idtac "p := "; print_exp p;
        idtac "lp := "; print_exp lp;
        idtac "t := "; print_exp (interpret_list t l);
        match t with
        | lceq (Pow ?p0 ?d)  (lceq ?c ?lc) =>
          let c := constr:(interpret c l) in
          match lc with
          | lceq ?c1 _ =>
            intros; exists (c * (interpret c1 l)); simplZ;
            let lc:= constr:(interpret_list lc l) in
            let p0 := constr:(interpret p0 l) in
            let e := constr:(combine lc lp) in
            let Hgb1 := fresh "Hgb" in
            let Hgb2 := fresh "Hgb" in
            cut (p = p0);
            [simplZ; intro Hgb1; try rewrite Hgb1; clear Hgb1;
             cut (c * p0 ^ (Zpos d) = e);
             [simplZ; idtac
             | simplZ; try ring]
            | simplZ; try ring];
            match goal with
            | |- ?a = ?b -> _ =>
              intro Hgb2; pattern a at 1;
              rewrite Hgb2; clear Hgb2;
              repeat equalities_to_goal2;
              repeat rewrite_with_goal_in_goal;
              ring
            end
          end
        | lceq (Const ?p0 ?d)  (lceq ?c ?lc) => (* d=0 *)
          let c := constr:(interpret c l) in
          match lc with
          | lceq ?c1  _ =>
            intros; exists (c * (interpret c1 l)); simplZ;
            let lc:= constr:(interpret_list lc l) in
            let e := constr:(combine lc lp) in
            let Hgb1 := fresh "Hgb" in
            cut (c=e);
            [simplZ; repeat equalities_to_goal2;
             repeat rewrite_with_goal_in_goal;
             intro Hgb1; ring_simplify in Hgb1;
             ring_simplify; auto
            | simplZ; try ring]
          end
        end
      )
    end
  | |- exists x : Z, exists y : Z, ?a = ?b * x + ?d * y =>
    apply gb_ex_ex2; gb_exists_original program
  | |- exists x : Z, exists y : Z, ?a = x * ?b + y * ?d =>
    repeat equalities_to_goal2;
    match goal with
    | |- ?g =>
      let lh := lhyps g in
      let t1 := constr:(a = 0) in
      let t := ajoute_hyps lh t1 in
      let t := constr:(b = 0 -> d = 0 -> t) in
      let l := variables t in
      let a := abstrait t l in
      let lp1 := constr:(List.rev (interpret_list a l))  in
      let p := constr:(List.hd 0 lp1) in
      let lp := constr:(List.rev (List.tail lp1)) in
      gbarith_compute program a ltac:(fun t =>
        match t with
        | lceq (Pow ?p0 ?d)  (lceq ?c ?lc) =>
          let c := constr:(interpret c l) in
          match lc with
          | lceq ?c1 (lceq ?c2 _) =>
            intros; exists (c * (interpret c1 l)); simplZ;
            intros; exists (c * (interpret c2 l)); simplZ;
            let lc:= constr:(interpret_list lc l) in
            let p0 := constr:(interpret p0 l) in
            let e := constr:(combine lc lp) in
            let Hgb1 := fresh "Hgb" in
            let Hgb2 := fresh "Hgb" in
            cut (p = p0);
            [simplZ; intro Hgb1; try rewrite Hgb1; clear Hgb1;
             cut (c * p0 ^ (Zpos d) = e);
             [simplZ; idtac
             | simplZ; try ring]
            | simplZ;try ring];
            match goal with
            | |- ?a = ?b -> _ =>
              intro Hgb2; pattern a at 1; rewrite Hgb2; clear Hgb2;
              repeat equalities_to_goal2; repeat rewrite_with_goal_in_goal;
              ring
            end
          end
        | lceq (Const ?p0 ?d)  (lceq ?c ?lc) => (* d=0 *)
          let c := constr:(interpret c l) in
          match lc with
          | lceq ?c1 (lceq ?c2 _) =>
            intros; exists (c * (interpret c1 l)); simplZ;
            intros; exists (c * (interpret c2 l)); simplZ;
            let lc := constr:(interpret_list lc l) in
            let e := constr:(combine lc lp) in
            let Hgb1 := fresh "Hgb" in
            cut (c = e);
            [simplZ; repeat equalities_to_goal2;
             repeat rewrite_with_goal_in_goal;
             intro Hgb1; ring_simplify in Hgb1; ring_simplify; auto
            | simplZ; try ring]
            end
        end
      )
    end
 end.

Ltac gb_get_goal :=
  match goal with
  | |- ?g => g
  end.

Ltac gb_rewrite f t :=
  let Hgb := fresh "Hgb" in
  cut (f = t); simplZ; [idtac | ring];
  match goal with
  | |- ?a = ?b -> _ =>
    intro Hgb; try pattern a at 1; try rewrite Hgb; clear Hgb
  end.

Ltac cancel_mult_div :=
  match goal with
    | |- context h [?b * (?a / ?b)] =>
      rewrite <- (Z_div_exact_full_2 a b);
      [ idtac
      | intro; discriminate
      | idtac]
    | |- context h [?b * (?c * (?a / ?b))] =>
      rewrite (Zmult_assoc b c (a / b));
      rewrite (Zmult_comm b c);
      rewrite <- (Zmult_assoc c b (a / b));
      cancel_mult_div
  end.

Ltac gb_exists1 program :=
  intros;
  repeat remove_exists_hyp;
  match goal with
  | |- exists x : Z, ?a = x * ?b =>
    apply gb_ex_ex1; gb_exists1 program
  | |- exists x : Z, ?a = ?b * x =>
    repeat equalities_to_goal2;
    let g := gb_get_goal in
    let lh := lhyps g in
    let t1:= constr:(a = 0) in
    let t := ajoute_hyps lh t1 in
    let t := constr:(b = 0 -> t) in
    let l := variables t in
    let abs := abstrait t l in
    let lp1 := constr:(List.rev (interpret_list abs l))  in
    let p := constr:(List.hd 0 lp1) in
    let lp := constr:(List.rev (List.tail lp1)) in
    idtac "t := "; print_exp t;
    gbarith_compute program abs ltac:(fun t =>
      idtac "variables := "; idtac l;
      idtac "abs := "; idtac abs;
      idtac "lp1 := "; print_exp lp1;
      idtac "p := "; print_exp p;
      idtac "lp := "; print_exp lp;
      idtac "t := "; idtac t;
      idtac "t := "; print_exp (interpret_list t l);
      match t with
      | lceq (Pow ?p0 1%positive) (lceq ?c ?lc) =>
        let c := constr:(interpret c l) in
        let c := eval compute in c in
        match lc with
        | lceq ?c1 _ =>
          let lc := constr:(interpret_list lc l) in
          let c1 := constr:(interpret c1 l) in
          let p0 := constr:(interpret p0 l) in
          let e := constr:(combine lc lp) in
          idtac "p0 := "; print_exp p0;
          idtac "c := "c;
          idtac "d := 1";
          idtac "lc := "; print_exp lc;
          idtac "c1 := "; print_exp c1;
          idtac "e := "; print_exp e;
          (* In this case,
           * - a = p = p0,
           * - c * p0 ^ (Zpos d) = e, and when d = 1
           * - p0 = b * (c1 / c)
           *)
          intros;
          match c with
          | 1%Z => exists c1
          | _ => (* exists (c1 / c) *) fail 100 "The constant c = "c" is not 1."
          end; (* check the constant c *)
          simplZ;
          gb_rewrite p p0; gb_rewrite p0 e;
          repeat equalities_to_goal2;
          repeat rewrite_with_goal_in_goal;
          ring
        end
      | lceq (Pow ?p0 1%positive) (lceq ?c ?lc) =>
        fail 100 "Tactic fails when d = 1."
      | lceq (Pow ?p0 ?d) (lceq ?c ?lc) =>
        fail 100 "d = "d" but only 1 is supported."
      | lceq (Const ?p0 ?d)  (lceq ?c ?lc) => (* d = 0, ?b = 1 *)
        let c := constr:(interpret c l) in
        let c := eval compute in c in
        match lc with
        | lceq ?c1  _ =>
          let lc := constr:(interpret_list lc l) in
          let c1 := constr:(interpret c1 l) in
          let e := constr:(combine lc lp) in
          idtac "p0 := "p0;
          idtac "c := "c;
          idtac "d := 0";
          idtac "lc := "; print_exp lc;
          idtac "c1 := "; print_exp c1;
          idtac "e := "; print_exp e;
          exists a; rewrite Z.mul_1_l; reflexivity
        end
      end (* end of match t *)
    )
  end.

Ltac gb_exists2 program :=
  intros;
  repeat remove_exists_hyp;
  match goal with
  | |- exists x : Z, exists y : Z, ?a = ?b * x + ?d * y =>
    apply gb_ex_ex2; gb_exists2 program
  | |- exists x : Z, exists y : Z, ?a = x * ?b + y * ?d =>
    repeat equalities_to_goal2;
    let g := gb_get_goal in
    let lh := lhyps g in
    let t1 := constr:(a = 0) in
    let t := ajoute_hyps lh t1 in
    let t := constr:(b = 0 -> d = 0 -> t) in
    let l := variables t in
    let abs := abstrait t l in
    let lp1 := constr:(List.rev (interpret_list abs l))  in
    let p := constr:(List.hd 0 lp1) in
    let lp := constr:(List.rev (List.tail lp1)) in
    idtac "t := "; print_exp t;
    gbarith_compute program abs ltac:(fun t =>
      match t with
      | lceq (Pow ?p0 1%positive)  (lceq ?c ?lc) =>
        let c := constr:(interpret c l) in
        let c := eval compute in c in
        match lc with
        | lceq ?c1 (lceq ?c2 _) =>
          (* this case is not tested *)
          let lc := constr:(interpret_list lc l) in
          let c1 := constr:(interpret c1 l) in
          let c2 := constr:(interpret c2 l) in
          let p0 := constr:(interpret p0 l) in
          let e := constr:(combine lc lp) in
          idtac "p0 := "; print_exp p0;
          idtac "c := "c;
          idtac "d := 1";
          idtac "lc := "; print_exp lc;
          idtac "c1 := "; print_exp c1;
          idtac "c2 := "; print_exp c2;
          idtac "e := "; print_exp e;
          match c with
          | 1%Z =>
            intros; exists c1; simplZ;
            intros; exists c2; simplZ
          | _ => fail 100 "The constant c = "c" is not 1."
          end;
          let Hgb1 := fresh "Hgb" in
          let Hgb2 := fresh "Hgb" in
          gb_rewrite p p0; gb_rewrite p0 e;
          repeat equalities_to_goal2;
          repeat rewrite_with_goal_in_goal;
          ring
        end
      | lceq (Pow ?p0 1%positive) (lceq ?c ?lc) =>
        fail 100 "Tactic fails when d = 1."
      | lceq (Pow ?p0 ?d) (lceq ?c ?lc) =>
        fail 100 "d = "d" but only 1 is supported."
      | lceq (Const ?p0 ?d)  (lceq ?c ?lc) => (* d = 0 *)
        let c := constr:(interpret c l) in
        let c := eval compute in c in
        match lc with
        | lceq ?c1 (lceq ?c2 _) =>
          let lc := constr:(interpret_list lc l) in
          let c1 := constr:(interpret c1 l) in
          let c2 := constr:(interpret c2 l) in
          let e := constr:(combine lc lp) in
          idtac "p0 = "; print_exp p0;
          idtac "c = "c;
          idtac "d = 0";
          idtac "lc = "; print_exp lc;
          idtac "c1 = "; print_exp c1;
          idtac "c2 = "; print_exp c2;
          idtac "e = "; print_exp e;
          match c with
          | 1%Z => intros; exists c1; simplZ; intros; exists c2; simplZ
          | _ => (* exists (c1 / c) *) fail 100 "The constant c = "c" is not 1."
          end; (* check the constant c *)
          let Hgb := fresh "Hgb" in
          cut (c = e); simplZ; [idtac | ring];
          repeat equalities_to_goal2;
          repeat rewrite_with_goal_in_goal;
          intro Hgb; ring_simplify in Hgb; ring_simplify; auto
        end
      end (* end of match t *)
    )
  end.

Ltac gb_exists program :=
  (gb_exists1 program) || (gb_exists2 program).

Definition divides (a b : Z) := exists c : Z, b = c * a.
Definition modulo (a b p : Z) := exists k : Z, a - b = k * p.
Definition ideal (x a b : Z) := exists u : Z, exists v : Z, x = u * a + v * b.
Definition gcd (g a b : Z) := divides g a /\ divides g b /\ ideal g a b.
Definition coprime (a b : Z):= exists u : Z, exists v : Z, 1 = u * a + v * b.

Ltac gbarith_unfold:=
  repeat (match goal with
          | H : (divides ?a ?b) |- _ => unfold divides in H
          | |- (divides ?a ?b) => unfold divides
          | H : (modulo ?a ?b ?c) |- _ => unfold modulo in H
          | |- (modulo ?a ?b ?c) => unfold modulo
          | H : (ideal ?a ?b ?c) |- _ => unfold ideal in H
          | |- (ideal ?a ?b ?c) => unfold ideal
          | H : (gcd ?a ?b ?c) |- _ => unfold gcd in H; decompose [and] H; clear H
          | |- (gcd ?a ?b ?c) => unfold gcd; split
          | H : (coprime ?a ?b) |- _ => unfold coprime in H
          | |- (coprime ?a ?b) => unfold coprime
          end).

Ltac gbarith_choice_original program :=
  try split;
  intros;
  gbarith_unfold;
  gb_exists_original program.

Ltac gbarith_choice program :=
  try split;
  intros;
  gbarith_unfold;
  gb_exists program.

Ltac gbarith_original :=
  gbarith_choice_original JCF1 ||
  gbarith_choice_original JCF2 ||
  gbarith_choice_original LT.

Ltac gbarith :=
  gbarith_choice SingularZ || gbarith_choice JCF1 || gbarith_choice JCF2 || gbarith_choice LT.
