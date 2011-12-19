(** This contains the implementation of a [CNF] module
   on lazy literals. *)
Require Import Quote List Ergo OrderedType.
Require Import BinPos LLazy.
Require Import Sets.
Require Import Cnf DoubleNegUtils Setoid.
Require Export CNFLazyCommon.

(** * The module [CNFRAW] 
   
   What the CNF module would be if it were operating on raw literals
   instead of well-formed literals. We define smart constructors
   for every logical construct (atomic, or, and, implication and 
   equivalence).

   Note that the proxy for [f \/ g] is [[[f;g]]] and its negation
   is [[[~f];[~g]]] which corresponds to intuition, similarly for the
   other logical operators.
   *)
Module CNFRAW.
  Import LLAZY.RAW.
(*   Definition mk_lit idx b := Lit (LITINDEX.L idx b). *)
  Definition mk_lit atom b := Lit (Some atom, b).
  Definition mk_true := ltrue.
  Definition mk_false := lfalse.
  Definition mk_or f g := Proxy 
    ((f::g::nil)::nil) 
    (((mk_not f)::nil)::((mk_not g)::nil)::nil).
  Definition mk_and f g := Proxy
    ((f::nil)::(g::nil)::nil)
    (((mk_not f)::(mk_not g)::nil)::nil).
  Definition mk_impl f g := mk_or (mk_not f) g.
  Definition mk_iff f g := mk_and (mk_impl f g) (mk_impl g f).
End CNFRAW.

(** * The module [CNFLAZY] *)
Module CNFLAZY <: CNFLAZY_INTERFACE.
  (** [CNFLAZY] will be be our [CNF] module on lazy literals.
     We start by including [CNFLAZYCOMMON] which defines the
     module [L] of literals as [LLAZY], and the necessary sets, etc. *)
  Include CNFLAZYCOMMON.
  
  Import LLAZY. Import CNFRAW.

  (** We can now lift the smart constructors of [CNFRAW] to [LLAZY] 
     by proving that they build well-formed literals when their 
     parameters are well-formed. *)
  Property wf_mk_lit : forall idx b, wf_lit (mk_lit idx b).
  Proof. intro; constructor. Qed.
  Definition mk_lit atom b : formula := 
    mk_literal (mk_lit atom b) (wf_mk_lit atom b).

  Definition mk_true : formula := ltrue.
  Definition mk_false : formula := lfalse.

  Identity Coercion t_of_t_ : RAW.t >-> RAW.t_.

  Lemma mk_not_size : 
    forall l, wf_lit l -> RAW.size (RAW.mk_not l) = RAW.size l.
  Proof.
    intros l Hl; destruct l; inversion Hl; simpl; auto.
  Qed.
 
  (** The constructor [mk_or] and [mk_and] can be lifted
     without issue. [mk_impl] can be defined in terms of
     [mk_or] and [mk_and] so it is straightforward as well.
     *)
  Property wf_mk_or : forall (l l' : t), wf_lit (mk_or l l').
  Proof.
    intros [x Hx] [y Hy]; unfold mk_or; simpl; constructor.
    reflexivity.
    simpl; rewrite !RAW.mk_not_invol; reflexivity.
    simpl; rewrite !mk_not_size; auto; omega.

    intros l t0 Hl Ht0. inversion Hl; subst; try contradiction.
    inversion Ht0; subst; simpl; auto.
    destruct H; subst; simpl; auto; contradiction.
    intros l t0 Hl Ht0. inversion Hl; subst.
    inversion Ht0; simpl in *; subst; simpl; try apply wf_mk_not; intuition.
    destruct H; subst; try contradiction.
    inversion Ht0; simpl in H; subst; simpl; try apply wf_mk_not; intuition.
  Qed.
  Definition mk_or (f g : t) : formula := 
    mk_literal (mk_or f g) (wf_mk_or f g).

  Property wf_mk_and : forall (l l' : t), wf_lit (mk_and l l').
  Proof.
    intros [x Hx] [y Hy]; unfold mk_and; simpl; constructor.
    reflexivity. 
    simpl; rewrite !RAW.mk_not_invol; reflexivity.
    simpl; rewrite !mk_not_size; auto; omega.

    intros l t0 Hl Ht0. inversion Hl; subst; try contradiction.
    inversion Ht0; subst; simpl; auto; contradiction.
    destruct H; subst; try contradiction.
    inversion Ht0; subst; simpl; auto; contradiction.
    intros l t0 Hl Ht0. inversion Hl; subst; try contradiction.
    inversion Ht0; subst; simpl; try apply wf_mk_not; auto.
    destruct H; simpl in *; subst; simpl; try apply wf_mk_not; intuition.
  Qed.
  Definition mk_and (f g : t) := 
    mk_literal (mk_and f g) (wf_mk_and f g).

  Property wf_mk_impl : forall (l l' : t), wf_lit (mk_impl l l').
  Proof.
    intros x y; unfold mk_impl; exact (wf_mk_or (mk_not x) y).
  Qed.
  Definition mk_impl (f g : t) := 
    mk_literal (mk_impl f g) (wf_mk_impl f g).

  (** The smart constructor for [mk_iff] is a bit less efficient
     than what we wished. Indeed, one would like to build the proxy
     [[[f;g];[~f;~g]]] for the formula [f <-> g]. But then there is 
     no way to choose a second parameter for the proxy that verifies
     the property with [negation]. Namely, [negation] is not involutive
     on such a proxy ; our workaround is thus to use [mk_and] and [mk_impl]
     which is correct but adds a level of proxy.
     *)
  Property wf_mk_iff : forall (l l' : t), wf_lit (mk_iff l l').
  Proof.
    intros x y; unfold mk_iff; 
      exact (wf_mk_and (mk_impl _ _) (mk_impl _ _)).
  Qed.
  Definition mk_iff (f g : t) :=
    mk_literal (mk_iff f g) (wf_mk_iff f g).

  (** Finally, the [make] function just takes a formula (ie, a lazy literal)
     [f] and returns the singleton clause [{{f}}]. *)
  Definition make (f : formula) : cset := singleton {f}.
  Property make_1 : 
    forall f, make f [=] singleton {f}.
  Proof.
    intro f; reflexivity.
  Qed.

  Definition cfl (ll : list (list L.t)) : cset := 
    (fold_right (fun l cl => add (fold_right add {} l) cl) {} ll).
  Property cfl_1 : 
    forall ll, cfl ll [=]
      (fold_right (fun l cl => 
        add (fold_right add {} l) cl) {} ll).
  Proof.
    intros; reflexivity.
  Qed.

  Definition interp : varmaps -> formula -> Prop := interp.

  (** Finally, we define a conversion function that applies our
     smart constructors recursively in order to build a [formula]
     out of a general formula [form]. 

     We also include a proof that the converted formula is equivalent
     to the original formula.
     *)
  Module Conversion.
    Fixpoint mk_form (f : fform) : formula :=
      match f with
        | FVar idx => mk_lit (LITINDEX.Atom idx) true
        | FNot (FVar idx) => mk_lit (LITINDEX.Atom idx) false
        | FEq s1 s2 => mk_lit (LITINDEX.Equation s1 s2) true
        | FNot (FEq s1 s2) => mk_lit (LITINDEX.Equation s1 s2) false
        | FTrue => mk_true
        | FFalse => mk_false
        | FAnd f g => mk_and (mk_form f) (mk_form g)
        | FOr f g => mk_or (mk_form f) (mk_form g)
        | FNot f => mk_not (mk_form f)
        | FImp f g => mk_impl (mk_form f) (mk_form g)
        | FIff f g => mk_iff (mk_form f) (mk_form g)
      end.

    Lemma mk_not_not :
      forall v f, ~~(interp v f <-> ~interp v (mk_not f)).
    Proof.
      exact mk_not_interp.
    Qed.
    Corollary not_mk_not :
      forall v f, ~~(~(interp v f) <-> interp v (mk_not f)).
    Proof.
      intros v f N.
      apply (mk_not_not v f); intro R; crewrite R N.
      apply (double_not (interp v (mk_not f))); intro R; crewrite R N.
      apply N; reflexivity.
    Qed.
    
    Ltac aapply H := apply H; try assumption.
    Theorem mk_form_equiv :
      forall v f, Ergo.well_typed_formula v f ->
        ~~(finterp v f <-> interp v (mk_form f)).
    Proof.
      intros v; induction f; unfold interp; simpl;
        try destruct IHf as [IH1 IH2]; intro Hwt; inversion_clear Hwt.
      (* - lits *)
      vm_compute; tauto.
      intro N; apply N; symmetry.
      unfold LLAZY.interp, RAW.interp; simpl.
      apply ModelsRingExt.eq_wt_iff; auto.
      rewrite <- (Term.has_type_is_type_of _ _ _ _ H); exact H.
      rewrite <- (Term.has_type_is_type_of _ _ _ _ H0); exact H0.
      (* - true and false *)
      vm_compute; tauto.
      vm_compute; tauto.
      (* - and *)
      intro N; aapply IHf1; intro IH1; aapply IHf2; intro IH2;
        clear IHf1 IHf2.
      apply N; rewrite IH1; rewrite IH2; clear N IH1 IH2.
      unfold LLAZY.interp; simpl; intuition.
      (* - or *)
      intro N; aapply IHf1; intro IH1; aapply IHf2; intro IH2;
        clear IHf1 IHf2.
      apply N; rewrite IH1; rewrite IH2; clear N IH1 IH2.
      unfold LLAZY.interp; simpl; intuition.
      (* - ~ *)
      intro N; aapply IHf; intro R; crewrite R N.
      apply (mk_not_not v (mk_form f)); 
        intro R; crewrite R N.
      revert N; destruct f; apply double_not.
      (* - -> *)
      intro N; aapply IHf1; intro IH1; aapply IHf2; intro IH2;
        clear IHf1 IHf2.
      apply (imp_def (finterp v f1) (finterp v f2));
        intro R; crewrite R N; rewrite IH2 in N; rewrite IH1 in N.
      apply (not_mk_not v (mk_form f1)); intro R; crewrite R N.
      apply N; clear IH1 IH2 N.
      unfold CNFRAW.mk_impl, interp, L.interp, RAW.interp; simpl.
      intuition.
      (* - <-> *)
      intro N; aapply IHf1; intro IH1; aapply IHf2; intro IH2;
        clear IHf1 IHf2.
      unfold iff at 2 in N.
      apply (imp_def (finterp v f1) (finterp v f2)); intro R1.
      apply (imp_def (finterp v f2) (finterp v f1)); intro R2.
      crewrite R1 N; crewrite R2 N; rewrite IH1 in N; rewrite IH2 in N.
      apply (not_mk_not v (mk_form f1)); intro R; crewrite R N.
      apply (not_mk_not v (mk_form f2)); intro R; crewrite R N.
      apply N; clear N IH1 IH2.
      unfold CNFRAW.mk_iff, L.interp, RAW.interp; simpl. intuition.
    Qed.

    Corollary cnf :
      forall v f, Ergo.well_typed_formula v f ->
        ~~(finterp v f <-> interp v (mk_form f)).
    Proof.
      exact mk_form_equiv.
    Qed.
  End Conversion.
End CNFLAZY.
