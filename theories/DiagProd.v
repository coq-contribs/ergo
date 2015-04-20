Require Import Containers.Sets Containers.SetProperties.

Generalizable All Variables.

Section WithOT.
  Context `{A_OT : OrderedType A}.

  Fixpoint diagProd_aux (l : list A) (acc : set (A * A)) :=
    match l with
      | nil => acc
      | a::q =>
        diagProd_aux q 
        (fold_left (fun acc b => {(a,b); acc}) q acc)
    end.
  Definition diagProd (S : set A) :=
    diagProd_aux (elements S) {}.

  Lemma rowProd_inv :
    forall (a : A) (l : list A) (acc : set (A * A)) (t u : A),
      In (t, u) (fold_left (fun acc b => add (a, b) acc) l acc)
      <-> In (t, u) acc \/ (t === a /\ InA _eq u l).
  Proof.
    intros a; intro l; pattern l; apply rev_ind; clear l; intros; simpl in *.
    intuition. inversion H1.
    rewrite fold_left_app; simpl.
    split; intro Hin.
    destruct (eq_dec t a) as [e|n].
    destruct (eq_dec u x) as [e'|n'].
    right; split;
      [| rewrite <- InA_rev; auto; rewrite rev_unit; constructor]; auto.
    assert (~ ((a, x) === (t, u))).
    intros abs; inversion abs; subst; intuition.
    assert (Hin' := add_3 H0 Hin); rewrite H in Hin'; destruct Hin'.
    left; assumption.
    right; split; [auto | 
      rewrite <- InA_rev; auto; rewrite rev_unit; constructor 2; 
        rewrite InA_rev; auto; tauto].
    assert (~ ((a, x) === (t, u))).
    intros abs; inversion abs; subst; intuition.
    assert (Hin' := add_3 H0 Hin); rewrite H in Hin'; destruct Hin'.
    left; assumption. right; intuition.
    destruct Hin as [Hin|Hin].
    apply add_2; rewrite H; left; exact Hin.
    destruct Hin as [H1 H2]; rewrite <- InA_rev in H2; auto; 
      rewrite rev_unit in H2.
    inversion H2; subst; [apply add_1 | apply add_2].
    constructor; auto.
    rewrite H; right; rewrite <- InA_rev; auto; split; assumption.
  Qed.

  Lemma diagProd_aux_inv : 
    forall l acc, sort _lt l -> forall t u, 
      In (t,u) (diagProd_aux l acc)
      <->
      In (t,u) acc \/ 
      (t <<< u /\ InA _eq t l /\ InA _eq u l).
  Proof.
    intro l; induction l.
    intros; simpl in *; intuition. inversion H1.
    intros acc Hsort u u'; simpl; inversion Hsort; subst.
    rewrite (IHl (fold_left (fun (acc0 : set (A * A)) (b : A) =>
      add (a, b) acc0) l acc)); auto.
    rewrite (InfA_alt (eqA := _eq)) in H2; auto.
    split; intros [Hin|Hin].
    rewrite (rowProd_inv a l acc u u') in Hin; destruct Hin.
    left; assumption. right; intuition.
    rewrite H0; apply H2; intuition.
    right; intuition.
    left; rewrite rowProd_inv; left; assumption.
    destruct Hin as [Hin1 [Hin2 Hin3]].
    inversion Hin2; subst.
    left; rewrite rowProd_inv; right; split; auto.
    inversion Hin3; subst; auto.
    rewrite H0 in Hin1; rewrite H3 in Hin1; 
      contradiction (lt_not_eq Hin1 (reflexivity a)).
    right; inversion Hin3; subst.
    contradiction (@lt_not_eq _ _ _ _ _ a a); [|reflexivity].
    transitivity u.
    apply H2; intuition.
    rewrite H3 in Hin1; exact Hin1.
    intuition.
  Qed.

  Corollary diagProd_iff :
    forall s t u, In (t,u) (diagProd s) <-> (In t s /\ In u s /\ t <<< u).
  Proof.
    intros s t u; unfold diagProd; rewrite diagProd_aux_inv.
    intuition; contradiction (empty_1 H0).
    exact (elements_3 s).
  Qed.

  Instance diagProd_m : Proper (_eq ==> _eq) diagProd.
  Proof.
    repeat intro; destruct a; rewrite 2diagProd_iff.
    rewrite H; reflexivity.
  Qed.
  Instance diagProd_subset_m : Proper (Subset ==> Subset) diagProd.
  Proof.
    repeat intro; destruct a; rewrite diagProd_iff in *.
    rewrite H in H0; auto.
  Qed.
End WithOT.
