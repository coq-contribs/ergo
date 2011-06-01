Require Import QArith Containers.OrderedTypeEx Eqdep_dec.
Require Export Qcanon.

Module QasDT <: DecidableType.
  Definition U := Q.
  Property eq_dec : forall (q q' : U), {q = q'} + {q <> q'}.
  Proof.
    intros; repeat decide equality.
  Qed.
End QasDT.
Module QEqDep := DecidableEqDep(QasDT).

Program Instance rational_UOT : UsualOrderedType Qc := {
  SOT_lt := Qclt;
  SOT_cmp := Qccompare
}.
Next Obligation.
  constructor.
  exact Qclt_trans.
  exact Qclt_not_eq.
Qed.
Next Obligation.
  destruct (x ?= y) as [ ]_eqn:H; constructor.
  rewrite Qceq_alt; exact H.
  rewrite Qclt_alt; exact H.
  rewrite <- Qcgt_alt in H; exact H.
Qed.
Definition rational_OT : OrderedType Qc :=
  @SOT_as_OT _ _ _ rational_UOT.
Existing Instance rational_OT.