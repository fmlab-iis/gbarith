
Add Rec LoadPath "../src/" as GBArith.
Add ML Path "../src/".

Require Import GBArithDef.
Require Import BinNums.

(*
Goal forall x y a b c : Z,
       x = y^2 + 1 ->
       b = (2^4) * a ->
       c = 3 * a ->
       modulo (x * b) (x * c) (x * 13).

variables :=
(c :: a :: b :: y :: x :: Datatypes.nil)

a :=
(lceq (Mul (Var 5) (Const 13 1))
   (lceq (Sub (Var 5) (Add (Pow (Var 4) 2) (Const 1 1)))
      (lceq (Sub (Var 3) (Mul (Pow (Const 2 1) 4) (Var 2)))
         (lceq (Sub (Var 1) (Mul (Const 3 1) (Var 2)))
            (lceq (Sub (Mul (Var 5) (Var 3)) (Mul (Var 5) (Var 1))) lnil)))))

lp1 :=
(x * b - x * c
 :: c - 3 * a :: b - 2 ^ 4 * a :: x - (y ^ 2 + 1) :: x * 13 :: Datatypes.nil)

p :=
(x * b - x * c)

lp :=
(x * 13 :: x - (y ^ 2 + 1) :: b - 2 ^ 4 * a :: c - 3 * a :: Datatypes.nil)

t :=
((- c + b) * x :: 3 :: c :: 0 :: 3 * x :: -16 * x :: Datatypes.nil)

p0 :=
((- c + b) * x)

d :=
1%positive

c :=
3

lc :=
(c :: 0 :: 3 * x :: -16 * x :: Datatypes.nil)

c1 :=
c
*)
Definition lp :=
  (lceq (Mul (Var 5) (Const 13 1))
    (lceq (Sub (Var 5) (Add (Pow (Var 4) 2) (Const 1 1)))
      (lceq (Sub (Var 3) (Mul (Pow (Const 2 1) 4) (Var 2)))
        (lceq (Sub (Var 1) (Mul (Const 3 1) (Var 2)))
          (lceq (Sub (Mul (Var 5) (Var 3)) (Mul (Var 5) (Var 1))) lnil))))).

Ltac test :=
  let lc := fresh "lc" in
  gbarith_compute 1 lc lp.

Lemma test_lemma : True.
Proof.
  test.
Qed.