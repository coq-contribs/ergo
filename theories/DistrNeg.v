(** This file gives the definition and properties
   of a function that negates lists of lists representing
   conjunctions of disjunctions. *)

Require Export DoubleNegUtils List SetoidList. 

Set Implicit Arguments.

(** We give a function calculating the interpretation 
   of lists of lists representing conjunctions of disjunctions. 
   *)
Section Interp.
  Variable A : Type.
  Definition l_interp (interp : A -> Prop) :=      
    (fix l_interp c :=
      match c with 
        | nil => False
        | l::q => (interp l) \/ (l_interp q)
      end).
  Definition ll_interp (interp : A -> Prop) :=
    (fix ll_interp ll := 
      match ll with
        | nil => True
        | c::q => (l_interp interp c) /\ (ll_interp q)
      end).
End Interp.

(** The [distr_neg] function negates its argument. *)
Section DistrNeg.
  Variable A : Type.
  Variable neg : A -> A.

  Fixpoint distr_neg (q : list (list A)) : list (list A) :=
    match q with
    | nil => cons nil nil
    | cons l q =>
      fold_right (fun a acc =>
        fold_right (fun l acc =>
          ((neg a)::l)::acc
        ) acc (distr_neg q)
      ) nil l
    end.
End DistrNeg.

(** [distr_neg] has a very fundamental property : given an interpretation
   function on literals, it computes the negation (in the sense of this
   interpretation) of a list of lists of literals. *)
Section Props.
  Variable A : Type.
  Variable mk_not : A -> A.
  Let negation := distr_neg mk_not.
  
  Variable f : A -> Prop.
  Definition cinterp := l_interp f.
  Definition pinterp := ll_interp f.
  
  Theorem negation_interp :
      forall p, 
        (forall l c, In l c -> In c p -> ~~(f l <-> ~f (mk_not l))) ->
        ~~(ll_interp f p <-> ~ll_interp f (negation p)).
  Proof.
    induction p.
    simpl; tauto.
    intros Hl N; elim IHp.
    intros l c H1 H2; apply (Hl l c); auto; constructor 2; auto.
    intro R; clear IHp; move N after R.
    unfold negation, distr_neg in N.
    fold (distr_neg mk_not p) in N; fold (negation p) in N.
    assert (Ha : forall l, In l a -> ~~(f l <-> ~ f (mk_not l))).
    intros l Hla; apply Hl with a; auto; constructor; auto.
    clear Hl; induction a as [|e q]; try move N after IHa.
    destruct p; apply N; simpl; tauto.
    elim IHq. intro Ra; move N after Ra; clear IHq.
    2:(intros l Hla0; apply Ha; auto; constructor 2; auto).
    simpl in N.
    set  (Z := 
      (fold_right
        (fun (a : A) (acc : list (list A)) =>
          fold_right
            (fun (l : list A) (acc0 : list (list A)) =>
              (mk_not a :: l) :: acc0) acc 
            (negation p)) nil q)).
    change (ll_interp f (q::p) <-> ~ll_interp f Z) in Ra.
    change (~ ((ll_interp f ((e::q)::p)) <->
      ~ ll_interp f
       (fold_right (fun (l : list A) (acc : list (list A)) =>
         (mk_not e :: l) :: acc)
       Z (negation p)))) in N.
    clearbody Z; move N after Ra.
    simpl in Ra, N.
    set (Q := negation p); fold Q in R, N; clearbody Q.
    rewrite R in *; clear R.
    (** pour faire apparaître pinterp v Z dans N *)
    assert (Rew :
      ll_interp f
      (fold_right
        (fun (l : list A) (acc : list (list A)) =>
          (mk_not e :: l) :: acc) Z Q) <->
      ll_interp f (fold_right (fun (l : list A) (acc : list (list A)) =>
        (mk_not e :: l) :: acc) nil Q)
      /\ ll_interp f Z).
    clear; induction Q; simpl.
    tauto.
    simpl; tauto.
(*     destruct (mem t full_eq_dec_ e a); simpl; tauto. *)
    (** -- *)
    crewrite Rew N.
    apply (not_and_or_not
      (ll_interp f (fold_right
        (fun (l : list A) (acc : list (list A)) =>
          (mk_not e :: l) :: acc)
        nil Q)) (ll_interp f Z)); intro R; crewrite R N.
    rewrite <- Ra in N; clear Ra.
    revert Ha N; clear; intros; induction Q.
    apply N; simpl; tauto.
    apply IHQ; intro IH; clear IHQ.
    move N after IH; simpl in N.
    apply (Ha e (or_introl _ (refl_equal e))); intro He; clear Ha.
    (** Cas où on ajoute bien la clause (le cas "standard") *)
    simpl in N, IH.
    apply (not_and_or_not 
      (f (mk_not e) \/ l_interp f a)
      (ll_interp f (fold_right
        (fun (l : list A) (acc : list (list A)) =>
          (mk_not e :: l) :: acc) nil Q))); intro R; crewrite R N.
    apply (not_or_and_not (f (mk_not e)) (l_interp f a));
      intro R; crewrite R N.
    apply (not_and_or_not (l_interp f a) (ll_interp f Q));
      intro R; crewrite R N.
    rewrite <- He in N; clear He.
    set (Z := ll_interp f (fold_right
      (fun (l : list A) (acc : list (list A)) =>
        (mk_not e :: l) :: acc) nil Q)). fold Z in IH, N; clearbody Z.
    apply N; clear N; split; intros.
    (** intuition mais lent *)
    decompose [and or] H.
    left; left; split; assumption.
    destruct (proj1 IH) as [H'|[H' H'']]. split; [left |]; assumption.
    left; right; assumption. right; split; [|right]; assumption.
    right; split; [|left]; assumption.
    right; split; [|right]; assumption.
    (** -- *)
    decompose [and or] H.
    split; left; assumption.
    destruct (proj2 IH) as [[H'|H'] H'']. left; assumption.
    split; [left | right]; assumption.
    split; right; assumption.
    split; [right | left]; assumption.
    split; right; assumption.
  Qed.
End Props.

(** [distr_neg] has some useful morphism and composition properties. *)
Section Morphisms.
  Variable A : Type.
  Variable neg : A -> A.

  Variable eq : A -> A -> Prop.
  Variable eq_refl : forall x, eq x x.
  Variable eq_sym : forall x y, eq x y -> eq y x.
  Variable eq_trans : forall x y z, eq x y -> eq y z -> eq x z.

  Hypothesis neg_m : forall l l', eq l l' -> eq (neg l) (neg l').

  Theorem distr_neg_m :
    forall ll ll', eqlistA (eqlistA eq) ll ll' ->
      eqlistA (eqlistA eq) (distr_neg neg ll) (distr_neg neg ll').
  Proof.
    induction ll; destruct ll'; simpl; intro Heq.
    constructor; constructor.
    inversion Heq. inversion Heq.
    inversion_clear Heq; subst.
    assert (IH := IHll ll' H0); clear IHll H0.
    revert l H; induction a; destruct l; simpl in *; intro Heq.
    constructor.
    inversion Heq. inversion Heq.
    inversion_clear Heq; subst.
    assert (IH' := IHa l H0); clear IHa H0.
    revert IH IH'.
    generalize (fold_right (fun (a2 : A) (acc : list (list A)) =>
      fold_right (fun (l2 : list A) (acc0 : list (list A)) =>
        (neg a2 :: l2) :: acc0) acc (distr_neg neg ll')) nil l).
    generalize (fold_right (fun (a2 : A) (acc : list (list A)) =>
      fold_right (fun (l2 : list A) (acc0 : list (list A)) =>
        (neg a2 :: l2) :: acc0) acc (distr_neg neg ll)) nil a0).
    generalize (distr_neg neg ll'); generalize (distr_neg neg ll). 
    assert (Hnot := neg_m H); revert Hnot H; clear. 
    intros E Enot L; induction L; intro L'; destruct L';
      intros c c' H h; inversion H; subst.
    simpl; assumption.
    simpl; constructor.
    constructor; assumption.
    apply IHL; assumption.
  Qed.

  Variable f : A -> Prop.
  Hypothesis f_m : forall l l', eq l l' -> (f l <-> f l').

  Theorem interp_m :
    forall ll ll', eqlistA (eqlistA eq) ll ll' -> 
      (ll_interp f ll <-> ll_interp f ll').
  Proof.
    induction ll; intro ll'; destruct ll'; simpl; 
      intro Heq; inversion Heq; subst.
    tauto.
    cut (l_interp f a <-> l_interp f l).
    intro cut; rewrite cut; rewrite (IHll _ H4); reflexivity.
    clear Heq; revert f_m l H2; clear; intro f_m; induction a; destruct l;
      simpl in *; intro Heq; inversion Heq; subst.
    tauto.
    rewrite (f_m H2); rewrite (IHa _ H4); reflexivity.
  Qed.
End Morphisms.

Section Morphisms2.
  Variable A : Type.
  Variables neg neg' : A -> A.

  Variable eq : A -> A -> Prop.
  Variable eq_refl : forall x, eq x x.
  Variable eq_sym : forall x y, eq x y -> eq y x.
  Variable eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  
  Hypothesis H : forall l, eq (neg l) (neg' l).
  
  Theorem distr_neg_f :
    forall ll, eqlistA (eqlistA eq) (distr_neg neg ll) (distr_neg neg' ll).
  Proof.
    induction ll; simpl.
    constructor; constructor.
    revert ll IHll; induction a; simpl; intros ll IHll.
    constructor.
    assert (IH := IHa ll IHll); clear IHa.
    revert IH IHll.
    generalize (fold_right (fun (a2 : A) (acc : list (list A)) =>
      fold_right (fun (l2 : list A) (acc0 : list (list A)) =>
        (neg' a2 :: l2) :: acc0) acc (distr_neg neg' ll)) nil a0).
    generalize (fold_right (fun (a2 : A) (acc : list (list A)) =>
      fold_right (fun (l2 : list A) (acc0 : list (list A)) =>
        (neg a2 :: l2) :: acc0) acc (distr_neg neg ll)) nil a0).
    generalize (distr_neg neg' ll); generalize (distr_neg neg ll). 
    assert (Hnot := H a); revert Hnot; clear.
    intros E L; induction L; intro L'; destruct L';
      intros c c' H h; inversion h; inversion H; subst; simpl.
    constructor.
    assumption.
    constructor. constructor; assumption.
    apply IHL; assumption.
    constructor. constructor; assumption.
    apply IHL; assumption.
  Qed.
End Morphisms2.

Section Compose.
  Variables A B : Type.
  Variables negA : A -> A.
  Variables negB : B -> B.

  Variable eqA : A -> A -> Prop.
  Variable eqA_refl : forall x, eqA x x.
  Variable eqA_sym : forall x y, eqA x y -> eqA y x.
  Variable eqA_trans : forall x y z, eqA x y -> eqA y z -> eqA x z.

  Hypothesis negA_m : forall l l', eqA l l' -> eqA (negA l) (negA l').

  Variable eqB : B -> B -> Prop.
  Variable eqB_refl : forall x, eqB x x.
  Variable eqB_sym : forall x y, eqB x y -> eqB y x.
  Variable eqB_trans : forall x y z, eqB x y -> eqB y z -> eqB x z.

  Hypothesis negB_m : forall l l', eqB l l' -> eqB (negB l) (negB l').

  Variable f : A -> B.
  Hypothesis f_commut : forall a, eqB (f (negA a)) (negB (f a)).

  Theorem negation_compose :
    forall ll, eqlistA (eqlistA eqB) 
      (map (map f) (distr_neg negA ll)) (distr_neg negB (map (map f) ll)).
  Proof.
    induction ll; simpl.
    constructor; constructor.
    revert ll IHll; induction a; simpl; intros ll IHll.
    constructor.
    assert (IH := IHa ll IHll); clear IHa.
    revert IH IHll.
    generalize ((fold_right (fun (a1 : B) (acc : list (list B)) =>
      fold_right
        (fun (l : list B) (acc0 : list (list B)) => (negB a1 :: l) :: acc0)
        acc (distr_neg negB (map (map f) ll))) nil (map f a0))).
    generalize (fold_right (fun (a1 : A) (acc : list (list A)) =>
      fold_right (fun (l0 : list A) (acc0 : list (list A)) =>
        (negA a1 :: l0) :: acc0) acc (distr_neg negA ll)) nil a0).
    generalize (distr_neg negB (map (map f) ll)).
    generalize (distr_neg negA ll).
    assert (Hnot := f_commut a); revert Hnot; clear.
    intros E L; induction L; intro L'; destruct L';
      intros c c' H h; inversion h; inversion H; subst; simpl.
    assumption.
    assumption.
    constructor. constructor; assumption.
    apply IHL; assumption.
    constructor. constructor; assumption.
    apply IHL; assumption.
  Qed.
End Compose.

Unset Implicit Arguments.