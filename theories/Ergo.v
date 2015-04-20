Declare ML Module "ergo_plugin".

Require Import Quote Term.

Record varmaps := mk_varmaps {
  varmaps_lits : varmap Prop;
  varmaps_vty : Term.type_env;
  varmaps_vsy : Term.term_env varmaps_vty
}.
Definition empty_maps : varmaps :=
  mk_varmaps Empty_vm Empty_vm Empty_vm.

Inductive form : Set :=
| TVar (_ : index)
| TTrue
| TFalse
| TAnd (_ _ : form)
| TOr (_ _ : form)
| TNot (_ : form)
| TImp (_ _ : form)
| TIff (_ _ : form).

Section Interp.
  Variable v : varmap Prop.
  Fixpoint interp (f : form) : Prop :=
    match f with
      | TVar i => varmap_find True i v
      | TTrue => True
      | TFalse => False
      | TAnd f1 f2 => (interp f1) /\ (interp f2)
      | TOr f1 f2 => (interp f1) \/ (interp f2)
      | TNot f => ~(interp f)
      | TImp f1 f2 => (interp f1) -> (interp f2)
      | TIff f1 f2 => (interp f1) <-> (interp f2)
    end.
End Interp.

Inductive fform : Set :=
| FVar (_ : index)
| FEq (u v : term)
| FTrue
| FFalse
| FAnd (_ _ : fform)
| FOr (_ _ : fform)
| FNot (_ : fform)
| FImp (_ _ : fform)
| FIff (_ _ : fform).

Section FInterp.
  Variable vm : varmaps.
  Let ty_env := varmaps_vty vm.
  Let t_env := varmaps_vsy vm.
  Let v := varmaps_lits vm.

  Fixpoint finterp (f : fform) : Prop :=
  match f with
    | FVar i => varmap_find True i v
    | FEq u v => Term.eq ty_env t_env u v
    | FTrue => True
    | FFalse => False
    | FAnd f1 f2 => (finterp f1) /\ (finterp f2)
    | FOr f1 f2 => (finterp f1) \/ (finterp f2)
    | FNot f => ~(finterp f)
    | FImp f1 f2 => (finterp f1) -> (finterp f2)
    | FIff f1 f2 => (finterp f1) <-> (finterp f2)
  end.
End FInterp.

Section Abstractions.
  Require Import List Bool.
  Variable vm : varmaps.
  Let ty_env := varmaps_vty vm.
  Let t_env := varmaps_vsy vm.
  Let v := varmaps_lits vm.

  Structure abstraction := {
    ty : type;
    ra : term;
    rb : term;
    Ha : has_type ty_env t_env ra ty = true;
    Hb : has_type ty_env t_env rb ty = true
  }.

  Fixpoint ainterp_eq (u v : term) (reifs : list abstraction) :=
    match reifs with
      | nil => Term.eq ty_env t_env u v
      | cons abs q =>
        let (ty, ra, rb, Ha, Hb) := abs in
          if term_equal ra u then
            if term_equal rb v then
              Term.interp ty_env t_env ra ty Ha =
              Term.interp ty_env t_env rb ty Hb
              else ainterp_eq u v q
            else ainterp_eq u v q
    end.

  Lemma ainterp_eq_is_finterp :
    forall a b reifs,
      ainterp_eq a b reifs <-> finterp vm (FEq a b).
  Proof.
    intros t u; induction reifs.
    reflexivity.
    simpl; destruct a.
    case_eq (term_equal ra0 t); intro eq1; [|exact IHreifs].
    case_eq (term_equal rb0 u); intro eq2; [|exact IHreifs].
    revert Ha0 Hb0; rewrite (term_equal_1 _ _ eq1),
      (term_equal_1 _ _ eq2) in *; intros; clear eq1 eq2.
    apply replace'.
  Qed.

  Variable reifs : list abstraction.
  Fixpoint ainterp (f : fform) : Prop :=
    match f with
      | FVar i => varmap_find True i v
      | FEq u v => ainterp_eq u v reifs
      | FTrue => True
      | FFalse => False
      | FAnd f1 f2 => (ainterp f1) /\ (ainterp f2)
      | FOr f1 f2 => (ainterp f1) \/ (ainterp f2)
      | FNot f => ~(ainterp f)
      | FImp f1 f2 => (ainterp f1) -> (ainterp f2)
      | FIff f1 f2 => (ainterp f1) <-> (ainterp f2)
    end.

  Theorem ainterp_is_finterp :
    forall f, ainterp f <-> finterp vm f.
  Proof.
    induction f; try (simpl; tauto).
    apply ainterp_eq_is_finterp.
  Qed.
End Abstractions.
Check ainterp_is_finterp.

Section Abstractions2.
  Require Import List Bool.
  Variable vm : varmaps.
  Let ty_env := varmaps_vty vm.
  Let t_env := varmaps_vsy vm.
  Let v := varmaps_lits vm.

  Definition binterp_eq (u v : term) :=
    let ty := Term.type_of ty_env t_env u in
      (match has_type ty_env t_env u ty as a,
         has_type ty_env t_env v ty as b
       return
           has_type ty_env t_env u ty = a ->
           has_type ty_env t_env v ty = b ->
           option Prop
       with
         | true, true => fun Ha Hb =>
           Some (Term.interp ty_env t_env u ty Ha =
             Term.interp ty_env t_env v ty Hb)
         | _, _ => fun _ _ => None
       end) (refl_equal _) (refl_equal _).

  Lemma binterp_eq_is_finterp :
    forall a b E, binterp_eq a b = Some E -> (E <-> finterp vm (FEq a b)).
  Proof.
    intros a b E H.
    assert (Hab :
      has_type ty_env t_env a (type_of ty_env t_env a) = true /\
      has_type ty_env t_env b (type_of ty_env t_env a) = true).
    unfold binterp_eq in H; simpl.
    set (tya := type_of ty_env t_env a) in *; clearbody tya.
    set (hta := has_type ty_env t_env a tya) in *.
    set (htb := has_type ty_env t_env b tya) in *.
    set (Za := Term.interp ty_env t_env a tya) in *; clearbody Za.
    set (Zb := Term.interp ty_env t_env b tya) in *; clearbody Zb.
    fold hta in Za; fold htb in Zb.
    destruct hta; destruct htb; simpl; auto; try discriminate.

    unfold finterp; simpl; fold ty_env; fold t_env.
    rewrite <- (replace' ty_env t_env  _ _
      (type_of ty_env t_env a) (proj1 Hab) (proj2 Hab)).
    revert H; unfold binterp_eq; simpl.
    set (tya := type_of ty_env t_env a) in *; clearbody tya.
    set (hta := has_type ty_env t_env a tya) in *.
    set (htb := has_type ty_env t_env b tya) in *.
    set (Za := Term.interp ty_env t_env a tya) in *; clearbody Za.
    set (Zb := Term.interp ty_env t_env b tya) in *; clearbody Zb.
    fold hta in Za; fold htb in Zb.
    destruct hta; destruct htb; simpl; auto; try (intros; discriminate).
    intro H; inversion H; subst.
    rewrite (BoolEqDep.UIP_refl true (proj1 Hab)).
    rewrite (BoolEqDep.UIP_refl true (proj2 Hab)).
    reflexivity.
  Qed.

  Fixpoint binterp (f : fform) : option Prop :=
    match f with
      | FVar i => Some (varmap_find True i v)
      | FEq u v => binterp_eq u v
      | FTrue => Some True
      | FFalse => Some False
      | FAnd f1 f2 =>
        match binterp f1, binterp f2 with
          | Some F1, Some F2 => Some (F1 /\ F2)
          | _, _ => None
        end
      | FOr f1 f2 =>
        match binterp f1, binterp f2 with
          | Some F1, Some F2 => Some (F1 \/ F2)
          | _, _ => None
        end
      | FNot f =>
        match binterp f with
          | Some F => Some (~F)
          | None => None
        end
      | FImp f1 f2 =>
        match binterp f1, binterp f2 with
          | Some F1, Some F2 => Some (F1 -> F2)
          | _, _ => None
        end
      | FIff f1 f2 =>
        match binterp f1, binterp f2 with
          | Some F1, Some F2 => Some (F1 <-> F2)
          | _, _ => None
        end
    end.

  Theorem binterp_is_finterp :
    forall f F, binterp f = Some F -> (F <-> finterp vm f).
  Proof.
    induction f; intro G; intro H;
      try (exact (binterp_eq_is_finterp u v0 G H));
        simpl; inversion H; try tauto;
          try (destruct (binterp f1); destruct (binterp f2); try discriminate;
            inversion_clear H; inversion_clear H1;
              rewrite (IHf1 P (refl_equal _)), (IHf2 P0 (refl_equal _));
                tauto).
    destruct (binterp f); try discriminate.
    inversion_clear H1; rewrite (IHf _ (refl_equal _)); tauto.
  Qed.

  (** The fact that [binterp] returns Some-thing is a notion of
     well-typedness for the concrete formula. We define well typedness
     inductively for ease of use, and relate it to [binterp]. *)
  Inductive well_typed_formula : fform -> Prop :=
  | wt_FVar : forall (v : index), well_typed_formula (FVar v)
  | wt_FEq : forall (u v : term) (ty : type),
    has_type ty_env t_env u ty = true ->
    has_type ty_env t_env v ty = true ->
    well_typed_formula (FEq u v)
  | wt_FTrue : well_typed_formula FTrue
  | wt_FFalse : well_typed_formula FFalse
  | wt_FAnd : forall f1 f2,
    well_typed_formula f1 -> well_typed_formula f2 ->
    well_typed_formula (FAnd f1 f2)
  | wt_FOr : forall f1 f2,
    well_typed_formula f1 -> well_typed_formula f2 ->
    well_typed_formula (FOr f1 f2)
  | wt_FNot : forall f,
    well_typed_formula f ->
    well_typed_formula (FNot f)
  | wt_FImp : forall f1 f2,
    well_typed_formula f1 -> well_typed_formula f2 ->
    well_typed_formula (FImp f1 f2)
  | wt_FIff : forall f1 f2,
    well_typed_formula f1 -> well_typed_formula f2 ->
    well_typed_formula (FIff f1 f2).

  Theorem well_typed_formula_iff_binterp :
    forall f, well_typed_formula f <-> exists F, binterp f = Some F.
  Proof.
    intro; split; intro.
    (* -> *)
    induction H; simpl.
    eexists; reflexivity.
    unfold binterp_eq.
    rewrite <- (has_type_is_type_of _ _ _ _ H).
    set (htu := has_type ty_env t_env u ty0) in *.
    set (htv := has_type ty_env t_env v0 ty0) in *.
    set (Zu := Term.interp ty_env t_env u ty0) in *; clearbody Zu.
    set (Zv := Term.interp ty_env t_env v0 ty0) in *; clearbody Zv.
    fold htu in Zu; fold htv in Zv.
    destruct htu; destruct htv; simpl; auto; try discriminate.
    eexists; reflexivity.
    eexists; reflexivity. eexists; reflexivity.
    destruct IHwell_typed_formula1; destruct IHwell_typed_formula2;
      rewrite H1, H2; eexists; reflexivity.
    destruct IHwell_typed_formula1; destruct IHwell_typed_formula2;
      rewrite H1, H2; eexists; reflexivity.
    destruct IHwell_typed_formula; rewrite H0; eexists; reflexivity.
    destruct IHwell_typed_formula1; destruct IHwell_typed_formula2;
      rewrite H1, H2; eexists; reflexivity.
    destruct IHwell_typed_formula1; destruct IHwell_typed_formula2;
      rewrite H1, H2; eexists; reflexivity.
    (* <- *)
    induction f; simpl in H; destruct H as [F HF].
    constructor.
    set (ty0 := type_of ty_env t_env u).
    constructor 2 with ty0; unfold binterp_eq in HF; fold ty0 in HF;
      set (htu := has_type ty_env t_env u ty0) in *;
        set (htv := has_type ty_env t_env v0 ty0) in *;
          set (Zu := Term.interp ty_env t_env u ty0) in *; clearbody Zu;
            set (Zv := Term.interp ty_env t_env v0 ty0) in *; clearbody Zv;
              fold htu in Zu; fold htv in Zv;
                destruct htu; destruct htv; simpl; auto; try discriminate.
    constructor. constructor.
    destruct (binterp f1); destruct (binterp f2); try discriminate HF;
      inversion HF; subst; constructor;
        [apply IHf1; eexists; reflexivity | apply IHf2; eexists; reflexivity].
    destruct (binterp f1); destruct (binterp f2); try discriminate HF;
      inversion HF; subst; constructor;
        [apply IHf1; eexists; reflexivity | apply IHf2; eexists; reflexivity].
    destruct (binterp f); try discriminate HF; inversion HF; subst;
      constructor; apply IHf; eexists; reflexivity.
    destruct (binterp f1); destruct (binterp f2); try discriminate HF;
      inversion HF; subst; constructor;
        [apply IHf1; eexists; reflexivity | apply IHf2; eexists; reflexivity].
    destruct (binterp f1); destruct (binterp f2); try discriminate HF;
      inversion HF; subst; constructor;
        [apply IHf1; eexists; reflexivity | apply IHf2; eexists; reflexivity].
  Qed.
End Abstractions2.
