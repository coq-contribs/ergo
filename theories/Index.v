(** This file defines [Quote.index] as an [OrderedType]. *)
Require Import Containers.OrderedType.
Require Import Quote.

(** * The module [INDEX] *)
Module INDEX.
  Definition t := index.

  (** [INDEX] implements [Quote.index] as an [OrderedType]. *)
  Definition eq (l l' : t) : Prop := l = l'.

  Definition lt (l l' : t) : Prop := 
    index_lt l l' = true.

  Fact eq_refl : forall x : t, eq x x.
  Proof. reflexivity. Qed.
  Fact eq_sym : forall x y : t, eq x y -> eq y x.
  Proof. intros; symmetry; auto. Qed.
  Fact eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof. intros; transitivity y; auto. Qed.
    
  Fact lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; intros x; induction x; destruct y; destruct z; simpl;
      try intuition; try (exact (IHx y z H H0)).
  Qed.
  Fact lt_not_eq : forall x y : t, lt x y -> ~ x = y.
  Proof.
    unfold lt; unfold eq; induction x; destruct y; simpl; 
      try intuition; try inversion H0; eauto.
  Qed.

  Fixpoint compare_ (x y : t) : comparison :=
    match x, y with
      | End_idx, End_idx => Eq
      | End_idx, _ => Lt
      | _, End_idx => Gt
      | Left_idx x', Left_idx y' => compare_ x' y'
      | Left_idx _, _ => Lt
      | _, Left_idx _ => Gt
      | Right_idx x', Right_idx y' => compare_ x' y'
    end.

  Property compare_1 : forall x y, compare_ x y = Eq -> x = y.
  Proof.
    induction x; destruct y; simpl; try (intros; discriminate).
    intro H; rewrite (IHx _ H); reflexivity.
    intro H; rewrite (IHx _ H); reflexivity.
    intro; reflexivity.
  Qed.
  Property compare_2 : forall x y, compare_ x y = Lt -> lt x y.
  Proof.
    induction x; destruct y; unfold lt; 
      simpl; try (intros; discriminate); auto.
    intro H; exact (IHx _ H).
    intro H; exact (IHx _ H).
  Qed.
  Property compare_3 : forall x y, compare_ x y = Gt -> lt y x.
  Proof.
    induction x; destruct y; unfold lt; simpl; 
      try (intros; discriminate); auto.
    intro H; exact (IHx _ H).
    intro H; exact (IHx _ H).
  Qed.
    
  Instance t_UOT : UsualOrderedType t := {
    SOT_lt := lt;
    SOT_cmp := compare_;
    SOT_StrictOrder := Build_StrictOrder _ _ _ _ lt_trans lt_not_eq
  }.
  Proof.
    intros; case_eq (compare_ x y); intro Hcomp; constructor;
      [apply compare_1 | apply compare_2 | apply compare_3]; auto.
  Defined.

  Definition t_OT : OrderedType t := SOT_as_OT.
  Existing Instance t_OT.
End INDEX.
