Add Rec LoadPath "../src/" as GBArith.
Add ML Path "../src/".

(** ==========  gbR ========== *)

From Coq Require Import Reals.
Open Scope R_scope.
From GBArith Require Import GBR.

Goal forall r r0 r1 : R,
    r  = 0 ->
    r0 = 0 ->
    r0 * r1 + 1  = 0 ->
    r - r0 = 0.
Proof.
  gbR.
Qed.

Goal forall x t : R,
    x^2 <> 1 ->
    x <> 1.
Proof.
  gbR.
Qed.

Goal forall x y z : R,
    x^2 + x * y = 0 ->
    y^2 + x * y = 0 ->
    x + y = 0.
Proof.
  gbR.
Qed.

Goal forall x y : R,
    x <> 0 -> y <> 0 -> x * y <> 0.
Proof.
  gbR.
Qed.

Goal forall a b c s1 s2 s3 : R,
    s1 = a + b + c ->
    s2 = a * b + b * c + a * c ->
    s3 = a * b * c ->
    a^3 - s1 * a^2 + s2 * a - s3 = 0.
Proof.
  Time gbR.
Qed.

Goal forall a b c d s1 s2 s3 s4 : R,
    s1 = a + b + c + d ->
    s2 = a * b + a * c + a * d + b * c + b * d + c * d ->
    s3 = a * b * c + b * c * d + c * d * a + d * a * b ->
    s4 = a * b * c * d ->
    a^4 - s1 * a^3 + s2 * a^2 - s3 * a + s4 = 0.
Proof.
  Time gbR.
Qed.

Goal forall a b c d e s1 s2 s3 s4 s5 : R,
    s1 = a + b + c + d + e ->
    s2 = a * b + a * c + a * d + a * e + b * c + b * d + b * e + c * d + c * e + d * e ->
    s3 = a * b * c + a * b * d + a * b * e + a * c * d + a * c * e + a * d * e + b * c * d + b * c * e + b * d * e + c * d * e ->
    s4 = a * b * c * d + a * b * c * e + a * b * d * e + a * c * d * e + b * c * d * e ->
    s5 = a * b * c * d * e ->
    a^5 - s1 * a^4 + s2 * a^3 - s3 * a^2 + s4 * a - s5 = 0.
Proof.
  Time gbR_choice SingularR.
Qed.

Record point : Type :=
  { X : R;
    Y : R }.

Definition colinear (C A B : point) :=
  exists a : R,
    (X C) = a * (X A) + (1 - a) * (X B) /\
    (Y C) = a * (Y A) + (1 - a) * (Y B).

Definition colinear2 (A B C : point) :=
  (X A) * (Y B) + (X B) * (Y C) + (X C) * (Y A)
  = (Y B) * (X C) + (Y C) * (X A) + (Y A) * (X B).

Ltac elimex :=
  match goal with
  | H : exists a : R, _ |- _  => elim H; clear H; intros
  | H : _ /\ _ |- _ => decompose [and] H; clear H
  end.

(* The following lemma can be proved with JCF1 quickly. *)
Lemma pappus : forall A B C A' B' C' D E F : point,
    (X A') = 0 -> (X B') = 0 -> (X C') = 0 ->
    (Y A) = 0 -> (Y B) = 0 -> (Y C) = 0 ->
    colinear D A B' -> colinear D A' B ->
    colinear E A C' -> colinear E A' C ->
    colinear F B C' -> colinear F B' C ->
    colinear2 D E F.
Proof.
  unfold colinear.
  unfold colinear2.
  intros.
  rewrite H in *;clear H.
  rewrite H0 in *;clear H0.
  rewrite H1 in *;clear H1.
  rewrite H2 in *;clear H2.
  rewrite H3 in *;clear H3.
  rewrite H4 in *;clear H4.
  repeat elimex.
  Set Printing Depth 10000.
  Time gbR_choice JCF1.
Qed.

(** ==========  gbZ ========== *)

Close Scope R_scope.
From Coq Require Import ZArith.
From GBArith Require Import GBZ.
Open Scope Z_scope.

Goal forall x y z : Z,
    x + y + z = 0 ->
    x * y + y * z + z * x = 0 ->
    x * y * z = 0 ->
    x = 0.
Proof.
  gbZ.
Qed.

Goal forall x y z u : Z,
  x + y + z + u = 0 ->
  x * y + y * z + z * u + u * x + x * z + u * y = 0 ->
  x * y * z + y * z * u + z * u * x + u * x * y = 0 ->
  x * y * z * u = 0 ->
  x = 0.
Proof.
  gbZ.
Qed.

Goal forall x y z u v:Z,
  x + y + z + u + v = 0 ->
  x*y + x*z + x*u + x*v + y*z + y*u + y*v + z*u + z*v + u*v = 0 ->
  x*y*z + x*y*u + x*y*v + x*z*u + x*z*v + x*u*v + y*z*u + y*z*v + y*u*v + z*u*v = 0 ->
  x*y*z*u + y*z*u*v + z*u*v*x + u*v*x*y + v*x*y*z = 0 ->
  x*y*z*u*v = 0 ->
  x = 0.
Proof.
  gbZ.
Qed.

Goal forall x y z : Z,
    x^2 + x * y = 0 ->
    y^2 + x * y = 0 ->
    x + y = 0.
Proof.
  gbZ.
Qed.

Goal forall r r0 r1 : Z,
    r  = 0 ->
    r0 = 0 ->
    r0 * r1 + 1  = 0 ->
    r - r0 = 0.
Proof.
  Time gbZ.
Qed.

Goal forall a b c s1 s2 s3 : Z,
    s1 = a + b + c ->
    s2 = a * b + b * c + a * c ->
    s3 = a * b * c ->
    a^3 - s1 * a^2 + s2 * a - s3 = 0.
Proof.
  Time gbZ.
Qed.

Goal forall a b c d s1 s2 s3 s4 : Z,
    s1 = a + b + c + d ->
    s2 = a * b + a * c + a * d + b * c + b * d + c * d ->
    s3 = a * b * c + b * c * d + c * d * a + d * a * b ->
    s4 = a * b * c * d ->
    a^4 - s1 * a^3 + s2 * a^2 - s3 * a + s4 = 0.
Proof.
  Time gbZ.
Qed.

(** ==========  gbzarith ========== *)

From GBArith Require Import GBZArith.

(* p = x^7 + y^7,
   lp = [x + y],
   d = 1,
   c = 1,
   c1 = y^6 - y^5x + y^4x^2 - y^3x^3 + y^2x^4 - yx^5 + x^6 *)
Goal forall x y : Z, divides (x + y) (x^7 + y^7).
Proof.
  gbarith.
Qed.

(* p = c,
   lp = [a; 1 - (x * a + x0 * b); b * c - x1 * a],
   d = 1,
   c = 1,
   c1 = x1 * x0 + c * x *)
Goal forall a b c : Z, divides a (b * c) -> coprime a b -> divides a c.
Proof.
  gbarith.
Qed.

Goal forall x y : Z, coprime (x * y) (x^2 + y^2) <-> coprime x y.
Proof.
  gbarith.
Qed.

(* p = x - y,
   lp = [n; x + a - (y + a) - x0 * n]
   d = 1,
   c = 1,
   c1 = x0 *)
Goal forall x y a n : Z, modulo (x + a) (y + a) n <-> modulo x y n.
Proof.
  gbarith.
Qed.

(* p = x,
   lp = [n; x - 0 - x0 * n],
   d = 1,
   c = 1,
   c1 = x0 *)
Goal forall x n : Z, modulo x 0 n <-> divides n x.
Proof.
  gbarith.
Qed.

Goal forall x y n : Z, modulo x y n -> (coprime n x <-> coprime n y).
Proof.
  gbarith.
Qed.

(* p = x,
   lp = [y; x - (x0 * a + x1 * b); b - x2 * x; a - x3 * x; b - x4 * y; a - x5 * y],
   d = 1,
   c = 1,
   c1 = x4 * x1 + x5 * x0 *)
Goal forall a b c x y : Z, gcd x a b -> divides y a -> divides y b -> divides y x.
Proof.
  gbarith.
Qed.

(* p = x - y,
   lp = [n; 1 - (x0 * a + x1 * n); a * x - a * y - x2 * n],
   d = 1,
   c = 1,
   c1 = (-y + x) * x1 + x2 * x0 *)
Goal forall a x y n : Z, modulo (a * x) (a * y) n -> coprime a n -> modulo x y n.
Proof.
  gbarith.
Qed.

(* p = a - b,
   lp = [d; b - x * d; a - x0 * d],
   d = 1,
   c = 1,
   c1 = x0 - x *)
Goal forall d a b : Z, divides d a -> divides d b -> divides d (a - b).
Proof.
  gbarith.
Qed.

(* p = c * b,
   lp = [c * a; b - x * a],
   d = 1,
   c = 1,
   c1 = x *)
Goal forall a b c : Z, divides a b -> divides (c * a) (c * b).
Proof.
  gbarith.
Qed.

(* p = a,
   lp = [d; a - x0 * (x * d)],
   d = 1,
   c = 1,
   c1 = x * x0 *)
Goal forall x d a : Z, divides (x * d) a -> divides d a.
Proof.
  gbarith.
Qed.

(* p = b * d,
   lp = [a * c; d - x * c; b - x0 * a],
   d = 1,
   c = 1,
   c1 = x0 * x *)
Goal forall a b c d : Z, divides a b -> divides c d -> divides (a * c) (b * d).
Proof.
  gbarith.
Qed.

Goal forall a b d : Z, coprime d a -> coprime d b -> coprime d (a * b).
Proof.
  gbarith.
Qed.

Goal forall a b d : Z, coprime d (a * b) -> coprime d a.
Proof.
  gbarith.
Qed.

(* p = r,
   lp = [m * n; 1 - (x * m + x0 * n); r - x1 * n; r - x2 * m],
   d = 1,
   c = 1,
   c1 = x2 * x0 + x1 * x *)
Goal forall m n r : Z, divides m r -> divides n r -> coprime m n -> divides (m * n) r.
Proof.
  gbarith.
Qed.

(* p = x * y - x' * y',
   lp = [n; y - y' - x0 * n; x - x' - x1 * n],
   d = 1,
   c = 1,
   c1 = x * x0 + x1 * y' *)
Goal forall x x' y y' n : Z, modulo x x' n -> modulo y y' n -> modulo (x * y) (x' * y') n.
Proof.
  gbarith.
Qed.

(* p = x - y,
   lp = [n; m - x0 * n; x - y - x1 * m],
   d = 1,
   c = 1,
   c1 = x1 * x0 *)
Goal forall x y m n : Z, modulo x y m -> divides n m -> modulo x y n.
Proof.
  gbarith.
Qed.

(* p = x - y,
   lp = [a * b; x - y - x0 * b; x - y - x1 * a; 1 - (x2 * a + x3 * b)],
   d = 1,
   c = 1,
   c1 = x3 * x1 + x2 * x0 *)
Goal forall a b x y : Z, coprime a b -> modulo x y a -> modulo x y b -> modulo x y (a * b).
Proof.
  gbarith.
Qed.

(* p = x^2 - y^2,
   lp = [x + y],
   d = 1,
   c = 1,
   c1 = -y + x *)
Goal forall x y : Z, modulo (x^2) (y^2) (x + y).
Proof.
  gbarith.
Qed.

(* p = (x + y) * (x - y),
   lp = [n; y^2 - a - x0 * n; x^2 - a - x1 * n],
   d = 1,
   c = 1,
   c1 = x1 - x0 *)
Goal forall x y a n : Z, modulo (x^2) a n -> modulo (y^2) a n -> divides n ((x + y) * (x - y)).
Proof.
  gbarith.
Qed.

(** ==========  Examples that cannot be proved by gbarith_original ========== *)

Goal
  forall a b c : Z,
    b - 16 * a = 0 ->
    c - 3 * a = 0 ->
    modulo b c 13.
Proof.
  gbarith_original.
  Undo.
  gbarith.
Qed.
