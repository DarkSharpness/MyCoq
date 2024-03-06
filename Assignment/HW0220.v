Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import PV.Intro.
Local Open Scope Z.

Definition opposite_sgn (x y: Z): Prop := x * y < 0.

Fact opposite_sgn_plus_2: forall x,
  opposite_sgn (x + 2) x ->
  x = -1.
Proof. unfold opposite_sgn. nia. Qed.

Fact opposite_sgn_odds: forall x,
  opposite_sgn (square x) x ->
  x < 0.
Proof. unfold opposite_sgn, square. lia. Qed.
