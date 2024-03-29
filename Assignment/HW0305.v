Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PV.InductiveType.
Require Import PV.RecurProp.
Require Import PV.Syntax.
Require Import PV.DenotationalSemantics.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       DntSem_SimpleWhile2.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

Example true_and_fact:
  forall e: expr_bool,
    [[ ETrue && e ]] ~=~ e.
Proof.
  intros.
  unfold bequiv; intros s.
  unfold_sem.
  simpl.
  reflexivity.
Qed.

Example lt_plus_one_and_fact:
  forall e: expr_bool,
    [[ "x" < "x" + 1 && e ]] ~=~ e.
Proof.
  intros.
  rewrite lt_plus_one_fact.
  apply true_and_fact.
Qed.
