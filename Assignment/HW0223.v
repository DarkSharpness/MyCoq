Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import PV.InductiveType.
Local Open Scope Z.

Lemma size_nonneg: forall t,
  0 <= tree_size t.
Proof.
  intros.
  induction t; simpl; lia.
Qed.

Lemma reverse_result_Node: forall t t1 k t2,
  tree_reverse t = Node t1 k t2 ->
  t = Node (tree_reverse t2) k (tree_reverse t1).
Proof.
  intros.
  assert(t = tree_reverse (Node t1 k t2)) as G.
{
  intros.
  rewrite <- reverse_involutive with t.
  f_equal.
  apply H.
}
  simpl tree_reverse in G.
  apply G.
Qed.

Fixpoint left_most (t: tree) (default: Z): Z :=
  match t with
  | Leaf => default
  | Node l n r => left_most l n
  end.

Fixpoint right_most (t: tree) (default: Z): Z :=
  match t with
  | Leaf => default
  | Node l n r => right_most r n
  end.

Lemma left_most_reverse: forall t default,
  left_most (tree_reverse t) default = right_most t default.
Proof.
  intros t.
  induction t; simpl.
  + reflexivity.
  + rewrite IHt2. reflexivity.
Qed.
