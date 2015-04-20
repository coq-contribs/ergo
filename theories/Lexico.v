Require Import Wf.
Require Import Wf_nat.

Require Import Relation_Definitions.

Section WfInclusion.
  Variable A : Type.
  Variables R1 R2 : A -> A -> Prop.

  Lemma Acc_incl : inclusion A R1 R2 -> forall z:A, Acc R2 z -> Acc R1 z.
  Proof.
    induction 2.
    apply Acc_intro; auto with sets.
  Defined.
  Hint Resolve Acc_incl.

  Theorem wf_incl : inclusion A R1 R2 -> well_founded R2 -> well_founded R1.
  Proof.
    unfold well_founded in |- *; auto with sets.
  Defined.
End WfInclusion.

Section Inverse_Image.
  Variables A B : Type.
  Variable R : B -> B -> Prop.
  Variable f : A -> B.

  Let Rof (x y:A) : Prop := R (f x) (f y).

  Remark Acc_lemma : forall y:B, Acc R y -> forall x:A, y = f x -> Acc Rof x.
  Proof.
    induction 1 as [y _ IHAcc]; intros x H.
    apply Acc_intro; intros y0 H1.
    apply (IHAcc (f y0)); try trivial.
    rewrite H; trivial.
  Defined.

  Lemma Acc_inverse_image : forall x:A, Acc R (f x) -> Acc Rof x.
  Proof.
    intros; apply (Acc_lemma (f x)); trivial.
  Defined.

  Theorem wf_inverse_image : well_founded R -> well_founded Rof.
  Proof.
    red in |- *; intros; apply Acc_inverse_image; auto.
  Defined.
End Inverse_Image.

(** This section's aim is to prove that the lexicographic product of [<] *)
Section Wf_lt_lexic.
  Definition lex2 (p p' : nat*nat) : Prop :=
    (fst p) < (fst p') \/
    (fst p) = (fst p') /\ (snd p) < (snd p').
  
  Variable A B : Type.
  Variable measA: A -> nat.
  Variable measB: B -> nat.
  
  Definition orderAB : (A*B) -> (A*B) -> Prop :=
    fun ab1 ab2 => 
      let (a1,b1) := ab1 in
        let (a2, b2) := ab2 in
          lex2 (measA a1, measB b1) (measA a2, measB b2).
  
  Theorem wf_lt_lexico : well_founded orderAB.
  Proof.
    intros [a b].
    set (acc_a := (Wf_nat.well_founded_ltof A measA) a).
    generalize b; clear b; induction acc_a as [a acc_a IHa].
    pose (gen := refl_equal (measA a)).
    intro b. generalize gen.
    cut (forall a0, measA a = measA a0 -> Acc orderAB (a0,b)).
    intros; auto.
    pattern b; refine (well_founded_ind 
      (Wf_nat.well_founded_ltof B measB) _ _ b).
    clear b; intros b IHb.
    constructor.
    intros [a1 b1] H2; destruct H2 as [H2 | H2]; simpl in H2.
    apply (IHa a1). unfold Wf_nat.ltof.
    rewrite H; assumption.
    destruct H2 as [H2 H3].
    apply (IHb b1). unfold Wf_nat.ltof.
    assumption.
    rewrite H2; assumption.
  Defined.
End Wf_lt_lexic.
