Require Import Quote List Ergo OrderedType.
Require Import BinPos LLazy Semantics.
Require Import Sets.

Delimit Scope sem_scope with sem.
Open Scope sem_scope.

Module SEMLAZY <: SEM_INTERFACE LLAZY.
  Import LLAZY.
  Definition model := varmaps.

  Definition model_as_fun_l : model -> LITINDEX.t -> Prop :=
    LITINDEX.interp.
  Definition model_as_fun : model -> LLAZY.t -> Prop :=
    LLAZY.interp.
  Coercion model_as_fun : model >-> Funclass.
  
  Local Notation "M [ l ]" := (model_as_fun M l)(at level 0).

  Property full : 
    forall (M : model) (l : LLAZY.t), ~~(~(M[l]) -> M[LLAZY.mk_not l]).
  Proof.
    intros; simpl.
    generalize (LLAZY.mk_not_interp M l).
    tauto.
  Qed.
  Property consistent : forall (M : model) l, M[l] -> ~(M[LLAZY.mk_not l]).
  Proof.
    intros; simpl.
    generalize (LLAZY.mk_not_interp M l).
    tauto.
  Qed.
  Property morphism : forall (M : model) l l', l === l' -> (M[l] <-> M[l']).
  Proof.
    intros M l l' H; destruct l; destruct l'; simpl in *.
    change (this0 = this1) in H.
    unfold model_as_fun, interp; simpl.
    subst; reflexivity.
  Qed.
  Property wf_true : forall (M : model), M[LLAZY.ltrue].
  Proof.
    intros; exact I.
  Qed.

  Property wf_expand_ : forall (M : model) l, RAW.interp M l ->
    (forall c, List.In c (RAW.expand l) -> exists l', 
      List.In l' c /\ RAW.interp M l').
  Proof.
    intros M l; pattern l.
    apply RAW.literal_ind2 with 
      (Pl := fun c =>  l_interp (RAW.interp M) c -> 
        exists l', List.In l' c /\ RAW.interp M l')
      (Pp := fun p => ll_interp (RAW.interp M) p -> 
        forall c, List.In c p -> 
          exists l', List.In l' c /\ RAW.interp M l'); intros; simpl in *.
    contradiction.
    auto.
    contradiction.
    destruct H1; subst.
    exists a; tauto.
    destruct (H0 H1) as [l' Hl']; exists l'; intuition.
    contradiction.
    destruct H2; subst.
    tauto.
    exact (H0 (proj2 H1) c H2).
  Qed.
  Property wf_expand_lift : forall M L EL,
    eqlistA (eqlistA RAW.eq) (map (map this) L) EL ->
    (forall c, List.In c EL -> exists l', List.In l' c /\ RAW.interp M l') ->
    (forall c, List.In c L -> exists l', List.In l' c /\ M[l']).
  Proof.
    intro M; induction L; intros; inversion_clear H1.
    destruct EL; inversion_clear H; clear H3 IHL; subst.
    assert (Hl := H0 l (or_introl _ (refl_equal _))); clear EL H0 L.
    revert c H1 Hl; induction l; intros; destruct c; inversion_clear H1.
    destruct Hl as [? [abs _]]; contradiction abs.
    destruct Hl as [l' [Hl' HMl]].
    destruct Hl'; subst.
    exists t0; split; [left; auto|].
    unfold model_as_fun, interp; simpl; rewrite H; assumption.
    destruct (IHl c H0) as [l'' Hl''].
    exists l'; split; assumption.
    exists l''; split; intuition.
    destruct EL; inversion_clear H.
    refine (IHL EL H3 _ c H2).
    intros; apply H0; right; auto.
  Qed.
  Corollary wf_expand : forall (M : model) l, M[l] -> 
    (forall c, List.In c (expand l) -> exists l', List.In l' c /\ M[l']).
  Proof.
    intros M [l wfl] Hl c Hexp.
    assert (Hexp_map := expand_map_map (mk_literal l wfl)).
    set (L := expand (mk_literal l wfl)) in *; clearbody  L.
    refine (wf_expand_lift _ _ _ Hexp_map _ _ Hexp).
    exact (wf_expand_ _ _ Hl).
  Qed.

(*   Section Creation. *)
(*     Parameter model_of :  *)
(*       forall (m : LLAZY.t -> Prop) *)
(*         (Hfull : forall l, ~~(~(m l) -> m (LLAZY.mk_not l))) *)
(*         (Hconsistent : forall l, m l -> ~(m (LLAZY.mk_not l))) *)
(*         (Hmorphism : forall l l', l === l' -> (m l <-> m l')) *)
(*         (Htrue : m ltrue) *)
(*         (Hexpand : forall l, m l ->  *)
(*           (forall c, List.In c (expand l) ->  *)
(*             exists l', List.In l' c /\ m l')), model. *)
    
(*     Axiom model_as_model_of :  *)
(*       forall m Hfull Hconsistent Hmorphism Htrue Hexpand l, *)
(*         model_as_fun  *)
(*         (model_of m Hfull Hconsistent Hmorphism Htrue Hexpand) l = m l. *)
(*   End Creation. *)

  Definition sat_clause (M : model) (C : clause) :=
    exists l, M[l] /\ l \In C.

  Definition sat_goal (M : model) (D : cset) :=
    forall C, C \In D -> sat_clause M C.

  Definition submodel (G : lset) (M : model) :=
    forall l, l \In G -> M[l].

  Definition incompatible (G : lset) (D : cset) :=
    forall (M : model), submodel G M -> ~sat_goal M D.
  
  Definition sat_clause_p (M : lset) (C : clause) :=
    exists l, l \In M /\ l \In C.

  Definition sat_goal_p (M : lset) (D : cset) :=
    forall C, C \In D -> sat_clause_p M C.

  (** Extra definitions and facts about equalities, only for SEMLAZY *)
  Require Import TermUtils.
  Definition equation (a b : term) : LLAZY.t :=
    LLAZY.mk_literal (LLAZY.RAW.Lit (Some (LITINDEX.Equation a b), true))
    (LLAZY.wf_lit_lit _).
  Definition disequation (a b : term) : LLAZY.t :=
    LLAZY.mk_literal (LLAZY.RAW.Lit (Some (LITINDEX.Equation a b), false))
    (LLAZY.wf_lit_lit _).

  (** [M] models a = b if [M (a = b)] *)
  Definition models_eq (M : model) (a b : term) := M (equation a b).
  Definition models_neq (M : model) (a b : term) := M (disequation a b).
  Notation "M |= a = b" := (models_eq M a b) 
    (at level 25, a at next level) : sem_scope.
  Notation "M |= a <> b" := (models_neq M a b) 
    (at level 25, a at next level) : sem_scope.

  (** This notion of truth for (dis)equalities has the intended properties *)
  Notation "t :> M" := (
    has_type (varmaps_vty M) (varmaps_vsy M) t
    (type_of (varmaps_vty M) (varmaps_vsy M) t) = true)(at level 0).
  Property models_eq_iff : forall M a b, a :> M -> b :> M ->
    (M |= a = b <-> eq (varmaps_vty M) (varmaps_vsy M) a b).
  Proof. 
    intros.
    exact (ModelsRingExt.eq_wt_iff M a b H H0).
  Qed.
  Property models_neq_iff : forall M a b, a :> M -> b :> M ->
    (M |= a <> b <-> (~eq (varmaps_vty M) (varmaps_vsy M) a b)).
  Proof. 
    intros.
    rewrite <- (ModelsRingExt.eq_wt_iff M a b H H0); reflexivity.
  Qed.

  Property models_eq_refl : forall M a, M |= a = a.
  Proof. exact ModelsRingExt.eq_refl. Qed.
  Property models_eq_sym : forall M a b, (M |= a = b) -> (M |= b = a).
  Proof. 
    intros M a b; exact (ModelsRingExt.eq_sym M b a). 
  Qed.
  Property models_eq_trans : forall M a b c, 
    M |= a = b -> M |= b = c -> M |= a = c.
  Proof. exact ModelsRingExt.eq_trans. Qed.

  Property models_neq_irrefl : forall M a, ~(M |= a <> a).
  Proof.
    intros; intro abs; exact (abs (models_eq_refl M a)).
  Qed.
  Property models_neq_sym : forall M a b,
    M |= a <> b -> M |= b <> a.
  Proof.
    repeat intro; apply H.
    exact (models_eq_sym M b a H0).
  Qed.

  (** [M] models a list of equations if it is a model of
     every equation in the list *)
  Inductive models_list (M : model) : list (term * term) -> Prop :=
  | models_list_nil : models_list M nil
  | models_list_cons :
    forall l a b, M |= a=b -> models_list M l -> models_list M ((a,b)::l).

  Definition models_list_iff :
    forall M l, models_list M l <-> 
      (forall e, List.In e l -> M |= (fst e) = (snd e)).
  Proof.
    intro M; induction l; split. 
    intros; contradiction.
    intros; constructor.
    intro H; inversion_clear H; intros [u v] Huv; 
      inversion_clear Huv; subst; simpl.
    inversion H; subst; auto.
    rewrite IHl in H1; apply (H1 (u, v) H).
    intros; destruct a as [u v]; constructor.
    apply (H (u, v)); left; reflexivity.
    rewrite IHl; intros; apply H; right; auto.
  Qed.
  Corollary models_list_in :
    forall M l u v, models_list M l -> 
      List.In (u, v) l -> M |= u = v.
  Proof.
    intros; rewrite models_list_iff in H; apply (H (u, v) H0).
  Qed.

  Property models_eq_congr : forall M f l l',
    list_eq (models_eq M) l l' -> M |= (app f l) = (app f l').
  Proof.
    intros; refine (ModelsRingExt.eq_congr M f l l' _).
    induction H; constructor; auto.
  Qed.

  (** Finally, entailment is defined as usual *)
  Definition entails (E : list (term * term)) (a b : term) :=
    forall M, models_list M E -> M |= a = b.
  Notation "E |- a = b" := (entails E a b) 
    (at level 25, a at next level) : sem_scope.
End SEMLAZY.