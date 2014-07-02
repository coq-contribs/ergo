(** This contains the implementation of a [CNF] module
   on lazy literals with n-ary constructors. *)
Require Import Omega Quote List Ergo OrderedType.
Require Import BinPos LLazy.
Require Import Sets List.
Require Import Cnf DoubleNegUtils Setoid.
Require Export CNFLazyCommon.

Section FormSize.
  Fixpoint size (f : fform) : nat :=
    match f with
      | FVar _ => 1
      | FEq _ _ => 1
      | FTrue => 1
      | FFalse => 1
      | FAnd f1 f2 => (size f1) + (size f2)
      | FOr f1 f2 => (size f1) + (size f2)
      | FNot f => S (size f)
      | FImp f1 f2 => (size f1) + (size f2)
      | FIff f1 f2 => (size f1) + (size f2)
    end.
  Definition form_size := size.

  Remark form_size_pos : forall f, form_size f > 0.
  Proof.
    induction f; simpl; auto with arith.
  Qed.
    
  Variable P : fform -> Type.
  Theorem form_size_induction : 
    (forall f, 
      (forall g, form_size g < form_size f -> P g) -> P f) -> 
    forall f, P f.
  Proof.
    apply Wf.well_founded_induction_type.
    apply Wf_nat.well_founded_ltof.
  Qed.
End FormSize.

(** * The module [CNFLAZYN] 

   A refined CNF module for lazy literals, where we add less level
   of proxies when constructing the formula thanks to n-ary constructors
   for disjunction and conjunction.

   For instance, the formula [F \/ (g \/ h)] will be a single proxy 
   [[[f;g;h]]] and its negation [[[~f];[~g];[~h]]], whereas in [CNFLAZY]
   there would have been two level of proxies. This is espexially critical
   on big formulas that are already in CNF.
   *)
Module CNFLAZYN <: CNFLAZY_INTERFACE.
  (** Again, we start by including the common part [CNFLAZYCOMMON]. *)
  Include CNFLAZYCOMMON.
  
  Import LLAZY.RAW. Import LLAZY.

  (** Definition of atomic smart constructors is no different than
     in [CNFLAZY]. *)
  Definition mk_lit_ idx b := Lit (Some idx, b).
(*   Definition mk_lit_ idx b := Lit (LITINDEX.L idx b). *)
  Property wf_mk_lit : forall idx b, wf_lit (mk_lit_ idx b).
  Proof. intro; constructor. Qed.
  Definition mk_lit idx b : formula := 
    mk_literal (mk_lit_ idx b) (wf_mk_lit idx b).

  Definition mk_true : formula := ltrue.
  Definition mk_false : formula := lfalse.

  Identity Coercion t_of_t_ : RAW.t >-> RAW.t_.

  Lemma mk_not_size : 
    forall l, wf_lit l -> RAW.size (RAW.mk_not l) = RAW.size l.
  Proof.
    intros l Hl; destruct l; inversion Hl; simpl; auto.
  Qed.

  (** The smart constructor for disjunction is now n-ary
     and takes a list of literals. *)
  Definition mk_or_ (lf : list t) := 
    let l := List.map this lf in
      Proxy
      (l::nil)
      (List.map (fun f => ((RAW.mk_not f)::nil)) l).
  Property wf_mk_or : forall (l : list t), wf_lit (mk_or_ l).
  Proof.
    induction l; unfold mk_or_; simpl.
    constructor.
    reflexivity. reflexivity. reflexivity.
    intros l t0 Hl Ht0; inversion Hl; subst; contradiction.
    intros l t0 Hl Ht0; inversion Hl; subst; contradiction.
    inversion IHl; constructor.
    rewrite <- H1; reflexivity.
    simpl; rewrite H2; simpl; rewrite RAW.mk_not_invol; reflexivity.
    simpl; rewrite (mk_not_size a (wf a)), <- H3; simpl; omega.
    intros l0 t0 Hl0 Ht0; inversion Hl0; subst.
    inversion Ht0; subst. exact (wf a).
    exact (H4 _ _ (or_introl _ (refl_equal _)) H).
    contradiction.
    intros l0 t0 Hl0 Ht0; inversion Hl0; subst.
    inversion Ht0; subst. exact (wf (mk_not a)).
    contradiction.
    exact (H5 l0 t0 H6 Ht0).
  Qed.
  Definition mk_or (lf : list formula) := 
    mk_literal (mk_or_ lf) (wf_mk_or lf).

  (** The same goes for the smart constructor for conjunction. *)
  Definition mk_and_ (lf : list t) :=
    let l := List.map this lf in
      Proxy 
      (List.map (fun f => cons f nil) l)
      ((List.map RAW.mk_not l)::nil).   
  Property wf_mk_and : forall (l : list t), wf_lit (mk_and_ l).
  Proof.
    induction l; unfold mk_and_; simpl. 
    constructor.
    reflexivity. reflexivity. reflexivity.
    intros l t0 Hl Ht0; inversion Hl; subst; contradiction.
    intros l t0 Hl Ht0; inversion Hl; subst; contradiction.
    inversion IHl; constructor.
    simpl; rewrite H1; simpl; reflexivity.
    simpl; rewrite <- H2, RAW.mk_not_invol; reflexivity.
    simpl; rewrite (mk_not_size a (wf a)), H3; simpl; omega.
    intros l0 t0 Hl0 Ht0; inversion Hl0; subst.
    inversion Ht0; subst. exact (wf a).
    contradiction.
    exact (H4 l0 t0 H6 Ht0).
    intros l0 t0 Hl0 Ht0; inversion Hl0; subst.
    inversion Ht0; subst. exact (wf (mk_not a)).
    exact (H5 _ _ (or_introl _ (refl_equal _)) H).
    contradiction.
  Qed.
  Definition mk_and (lf : list formula) := 
    mk_literal (mk_and_ lf) (wf_mk_and lf).

  (** Then, implication and equivalence are treated similarly as before.
     Maybe we could try an nary equivalence constructor ; this doesnt make
     sense for implication though, since it is not associative. 
     *)
  Definition mk_impl_ f g := mk_or ((mk_not f)::g::nil).
  Property wf_mk_impl : forall l l', wf_lit (mk_impl_ l l').
  Proof.
    intros x y; unfold mk_impl_; exact (wf_mk_or ((mk_not x)::y::nil)).
  Qed.
  Definition mk_impl (f g : formula) := 
    mk_literal (mk_impl_ f g) (wf_mk_impl f g).

  Definition mk_iff_ f g := mk_and_ ((mk_impl f g)::(mk_impl g f)::nil).
  Property wf_mk_iff : forall (l l' : t), wf_lit (mk_iff_ l l').
  Proof.
    intros x y; unfold mk_iff_; 
      exact (wf_mk_and ((mk_impl _ _)::(mk_impl _ _)::nil)).
  Qed.
  Definition mk_iff (f g : formula) :=
    mk_literal (mk_iff_ f g) (wf_mk_iff f g).

  (** The function [make] is the same as before. *)
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
  Definition or_interp v :=      
    (fix l_interp c :=
      match c with 
        | nil => False
        | l::q => (interp v l) \/ (l_interp q)
      end).
  Definition and_interp v :=
    (fix l_interp ll := 
      match ll with
        | nil => True
        | l::q => (interp v l) /\ (l_interp q)
      end).

  (** Finally, it is a bit more tricky to perform the conversion
     and to prove it is correct. We need auxiliary functions that
     try to extract as much top-level disjunctive/conjunctive structure
     that a formula may have in order to take advantage of the nary
     constructors.

     With a couple more proofs, we are again able to prove the
     logical equivalence between a formula and its conversion. *)
  Module Conversion.
    Definition mk_and_list (mk : fform -> formula) :=
      (fix mk_and_list (f : fform) (acc : list formula) :=
        match f with
          | FAnd f g => mk_and_list f (mk_and_list g acc)
          | FIff f g => 
            let F := mk f in let G := mk g in
              (mk_impl F G)::(mk_impl G F)::acc
          | _ => (mk f)::acc
        end).
    Definition mk_or_list (mk : fform -> formula) :=
      (fix mk_or_list (f : fform) (acc : list formula) :=
        match f with
          | FOr f g => mk_or_list f (mk_or_list g acc)
          | FImp f g => mk_or_list g ((mk_not (mk f))::acc)
(*           | TIff f g =>  *)
(*             (mk_and (mk_and_list mk f (mk_and_list mk g nil))):: *)
(*             (mk_and ((mk_not (mk f))::((mk_not (mk g))::nil)))::acc *)
          | FIff f g => 
            let F := mk f in let G := mk g in
              (mk_and (F::G::nil))::(mk_and ((mk_not F)::(mk_not G)::nil))::acc
          | _ => (mk f)::acc
        end).
    
    Fixpoint mk_form (f : fform) : formula :=
      match f with
        | FVar idx => mk_lit (LITINDEX.Atom idx) true
        | FNot (FVar idx) => mk_lit (LITINDEX.Atom idx) false
        | FEq s1 s2 => mk_lit (LITINDEX.Equation s1 s2) true
        | FNot (FEq s1 s2) => mk_lit (LITINDEX.Equation s1 s2) false
        | FTrue => mk_true
        | FFalse => mk_false
        | FAnd f g => mk_and 
          (mk_and_list mk_form f (mk_and_list mk_form g nil))
        | FOr f g => mk_or
          (mk_or_list mk_form f (mk_or_list mk_form g nil))
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

    Ltac aapply H := apply H ; try assumption.
    Hint Constructors well_typed_formula.
    Theorem mk_and_equiv :
      forall v f (l : list LLAZY.t),
        Ergo.well_typed_formula v f ->
        (forall g, form_size g <= form_size f -> well_typed_formula v g ->
          ~~(finterp v g <-> interp v (mk_form g))) ->
        ~~(finterp v f /\
          pinterp v
          (map (fun f => f :: nil) (map LLAZY.this l)) <->
          pinterp v
          (map (fun f => f :: nil)
            (map LLAZY.this (mk_and_list mk_form f l)))).
    Proof.
      intros v f; induction f; intros l Hwf IH N; inversion_clear Hwf.
      (* - lits, true and false *)
      apply N; clear N IH; simpl; tauto.
      apply N; clear N IH; simpl.
      rewrite (Term.has_type_is_type_of _ _ _ _ H) in H.
      rewrite (Term.has_type_is_type_of _ _ _ _ H0) in H0.
      generalize (ModelsRingExt.eq_wt_iff v u v0 H H0); tauto.
      apply N; clear N IH; simpl; tauto.
      apply N; clear N IH; simpl; tauto.
      (* - and (rec. case) *)
      simpl in *.
      aapply (IHf2 l); [| intro IH2; clear IHf2].
      intros g Hg; apply (IH g); rewrite Plus.plus_comm; auto with arith.
      aapply (IHf1 (mk_and_list mk_form f2 l)); [| intro IH1; clear IHf1].
      intros g Hg; apply (IH g); auto with arith.
      apply N; clear N IH; rewrite <- IH1.
      cut (forall A B C, (A /\ B) /\ C <-> A /\ (B /\ C)); [|tauto].
      intro cut; rewrite cut; rewrite IH2; tauto.
      (* - or *)
      aapply (IH (FOr f1 f2)); auto; intro R; crewrite R N.
      apply N; clear.
      unfold mk_and_list; generalize (mk_form (FOr f1 f2)); intro g.
      simpl; tauto.
      (* - not *)
      aapply (IH (FNot f)); auto; intro R; crewrite R N.
      apply N; clear.
      unfold mk_and_list; generalize (mk_form (FNot f)); intro g.
      simpl; tauto.
      (* - impl *)
      aapply (IH (FImp f1 f2)); auto; intro R; crewrite R N.
      apply N; clear.
      unfold mk_and_list; generalize (mk_form (FImp f1 f2)); intro g.
      simpl; tauto.
      (* - iff *)
      aapply (IH f1); simpl; auto with arith; intro R1.
      aapply (IH f2); simpl; auto with arith; intro R2.
      simpl finterp in N; crewrite R1 N; crewrite R2 N.
      unfold iff in N at 2.
      apply (imp_def (interp v (mk_form f1)) (interp v (mk_form f2)));
        intro R; crewrite R N.
      apply (imp_def (interp v (mk_form f2)) (interp v (mk_form f1)));
        intro R; crewrite R N.
      apply (not_mk_not v (mk_form f1)); intro N1.
      apply (not_mk_not v (mk_form f2)); intro N2.
      simpl in N; crewrite N1 N; crewrite N2 N.
      apply N; clear; tauto.
    Qed.
      
    Theorem mk_or_equiv :
      forall v f l,
        Ergo.well_typed_formula v f ->
        (forall g, form_size g <= form_size f -> well_typed_formula v g ->
          ~~(finterp v g <-> interp v (mk_form g))) ->
        ~~(finterp v f \/
          (cinterp v (map LLAZY.this l))
          <->
          cinterp v (map LLAZY.this (mk_or_list mk_form f l))).
    Proof.
      intros v f; induction f; intros l Hwf IH N; inversion_clear Hwf.
      (* - lits, true and false *)
      apply N; clear N IH; simpl; tauto.
      apply N; clear N IH; simpl.
      rewrite (Term.has_type_is_type_of _ _ _ _ H) in H.
      rewrite (Term.has_type_is_type_of _ _ _ _ H0) in H0.
      generalize (ModelsRingExt.eq_wt_iff v u v0 H H0); tauto.
      apply N; clear N IH; simpl; tauto.
      apply N; clear N IH; simpl; tauto.
      (* - and (rec. case) *)
      aapply (IH (FAnd f1 f2)); auto; intro R; crewrite R N.
      apply N; clear.
      unfold mk_or_list; generalize (mk_form (FAnd f1 f2)); intro g.
      simpl; tauto.
      (* - or (rec. case) *)
      simpl in *.
      aapply (IHf2 l); [| intro IH2; clear IHf2].
      intros g Hg; apply (IH g); rewrite Plus.plus_comm; auto with arith.
      aapply (IHf1 (mk_or_list mk_form f2 l)); [| intro IH1; clear IHf1].
      intros g Hg; apply (IH g); auto with arith.
      apply N; clear N IH; rewrite <- IH1.
      cut (forall A B C, (A \/ B) \/ C <-> A \/ (B \/ C)); [|tauto].
      intro cut; rewrite cut; rewrite IH2; tauto.
      (* - not *)
      aapply (IH (FNot f)); auto; intro R; crewrite R N.
      apply N; clear.
      unfold mk_or_list; generalize (mk_form (FNot f)); intro g.
      simpl; tauto.
      (* - impl *)
      aapply (IHf2 (LLAZY.mk_not (mk_form f1) :: l)); [|intro IH2; clear IHf2].
      intros g Hg; apply (IH g); simpl; omega.
      rewrite <- IH2 in N; clear IH2.
      apply (IH f1); simpl; auto with arith; intro R1.
      apply (IH f2); simpl; auto with arith; intro R2.
      simpl finterp in N; crewrite R1 N; crewrite R2 N.
      apply (imp_def (interp v (mk_form f1)) (interp v (mk_form f2)));
        intro R; crewrite R N.
      apply (not_mk_not v (mk_form f1)); intro N1; crewrite N1 N.
      apply N; clear; simpl; tauto.
      (* - iff *)
      apply (IH f1); simpl; auto with arith; intro R1.
      apply (IH f2); simpl; auto with arith; intro R2.
      simpl finterp in N; crewrite R1 N; crewrite R2 N.
      apply (iff_def (interp v (mk_form f1)) (interp v (mk_form f2)));
        intro R; crewrite R N.
      simpl in N.
      apply (not_mk_not v (mk_form f1)); intro N1.
      apply (not_mk_not v (mk_form f2)); intro N2.
      simpl in N; crewrite N1 N; crewrite N2 N.
      apply N; clear; tauto.
    Qed.

    Theorem mk_form_equiv :
      forall v f, Ergo.well_typed_formula v f ->
        ~~(finterp v f <-> interp v (mk_form f)).
    Proof.
      intros v.
      apply (@form_size_induction (fun f =>
        well_typed_formula v f -> ~~ (finterp v f <-> interp v (mk_form f)))). 
      intros f IH Hwt; destruct f; inversion_clear Hwt; unfold interp; simpl.
      (* - lits *)
      vm_compute; tauto.
      intro N; apply N; symmetry.
      unfold LLAZY.interp, RAW.interp; simpl.
      apply ModelsRingExt.eq_wt_iff; auto.
      rewrite <- (Term.has_type_is_type_of _ _ _ _ H); exact H.
      rewrite <- (Term.has_type_is_type_of _ _ _ _ H0); exact H0.
      (* - true and false *)
      tauto.
      vm_compute; tauto.
      (* - and *)
      intro N.
      aapply (mk_and_equiv v f2 nil); [| intro R2].
      intros g Hg; apply IH; simpl. assert (Hg' := form_size_pos f1).
      replace (form_size g) with (0 + form_size g); auto.
      apply Plus.plus_lt_le_compat; auto.
      (* omega should ve done the trick, weird thing going on there *)
      aapply (mk_and_equiv v f1
        (mk_and_list mk_form f2 nil)); [| intro R1].
      intros g Hg; apply IH; simpl. assert (Hg' := form_size_pos f2).
      replace (form_size g) with (form_size g + 0); auto.
      apply Plus.plus_le_lt_compat; auto.
      rewrite <- R1 in N; rewrite <- R2 in N; clear R1 R2.
      apply N; simpl; tauto.
      (* - or *)
      intro N.
      aapply (mk_or_equiv v f2 nil); [| intro R2].
      intros g Hg; apply IH; simpl. assert (Hg' := form_size_pos f1).
      replace (form_size g) with (0 + form_size g); auto. 
      apply Plus.plus_lt_le_compat; auto.
      aapply (mk_or_equiv v f1 (mk_or_list mk_form f2 nil)); [| intro R1].
      intros g Hg; apply IH; simpl. assert (Hg' := form_size_pos f2).
      replace (form_size g) with (form_size g + 0); auto.
      apply Plus.plus_le_lt_compat; auto.
      unfold LLAZY.interp, RAW.interp in N; simpl in N.
      rewrite <- R1 in N; rewrite <- R2 in N; clear R1 R2.
      apply N; simpl; tauto.
      (* - not *)
      intro N; aapply (IH f). simpl; auto.
      intro R; crewrite R N.
      apply (mk_not_not v (mk_form f)); intro R; crewrite R N.
      revert N; destruct f; apply double_not.
      (* - impl *)
      intro N.
      aapply (IH f1). simpl; generalize (form_size_pos f2); omega. intro R1.
      aapply (IH f2). simpl; generalize (form_size_pos f1); clear; omega.
      intro R2.
      apply (imp_def (finterp v f1) (finterp v f2)).
      intro R; crewrite R N; rewrite R2 in N; rewrite R1 in N.
      apply (not_mk_not v (mk_form f1)); intro R; crewrite R N.
      apply N; clear R1 R2 N.
      unfold interp, L.interp, RAW.interp; simpl.
      intuition.
      (* - iff *)
      intro N.
      aapply (IH f1). simpl; generalize (form_size_pos f2); omega. intro IH1.
      aapply (IH f2). simpl; generalize (form_size_pos f1); clear; omega.
      intro IH2.
      unfold iff at 2 in N.
      apply (imp_def (finterp v f1) (finterp v f2)); intro R1.
      apply (imp_def (finterp v f2) (finterp v f1)); intro R2.
      crewrite R1 N; crewrite R2 N; rewrite IH1 in N; rewrite IH2 in N.
      apply (not_mk_not v (mk_form f1)); intro R; crewrite R N.
      apply (not_mk_not v (mk_form f2)); intro R; crewrite R N.
      apply N; clear N IH1 IH2.
      unfold L.interp, RAW.interp; simpl.
      intuition.
    Qed.

    Corollary cnf :
      forall v f, well_typed_formula v f ->
        ~~(finterp v f <-> interp v (mk_form f)).
    Proof.
      exact mk_form_equiv.
    Qed.
  End Conversion.

End CNFLAZYN.