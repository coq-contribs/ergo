Require Import Env LLazy SemLazy CNFLazyCommon.
Require Import Containers.Sets Containers.SetProperties CCX.

Set Implicit Arguments.
Unset Strict Implicit.

Module ENVLAZY (Import F : CNFLAZY_INTERFACE) (CC : CCX_SIG)
  <: ENV_INTERFACE F.
  Import LLAZY. 

  Record t_ : Type := Build_t {
    (** - uninterpreted literals which have been added to the environment *)
    env : set LLAZY.t;
    (** - the CC environment *)
    cc : CC.t
  }.
  Definition t := t_.

  Definition empty := Build_t {LLAZY.ltrue} CC.empty.
  
  Definition oapply (f : CC.t -> Exception CC.t) (e : t) : Exception t :=
    let (env, cc) := e in
    match f cc with 
      | Inconsistent => Inconsistent
      | Normal cc' => Normal (Build_t env cc')
    end.
         
  Definition assume (l : LLAZY.t) (e : t) : Exception t :=
    match this l with
      | RAW.Lit (Some (LITINDEX.Equation u v), true) =>
        oapply (CC.assume (CCX.Equation u v)) e
      | RAW.Lit (Some (LITINDEX.Equation u v), false) =>
        oapply (CC.assume (CCX.Disequation u v)) e
      | _ => 
        if LLAZY.mk_not l \in env e then Inconsistent 
          else Normal (Build_t {l; env e} (cc e))
    end.

  Definition query (l : LLAZY.t) (e : t) : bool :=
    match this l with
      | RAW.Lit (Some (LITINDEX.Equation u v), true) =>
        CC.query (Equation u v) (cc e)
      | RAW.Lit (Some (LITINDEX.Equation u v), false) =>
        CC.query (Disequation u v) (cc e)
      | _ => l \in env e
    end.
        
  (** Specification *)
  Definition is_prop (l : LLAZY.t) :=
    match this l with
      | LLAZY.RAW.Lit (Some (LITINDEX.Equation _ _), _) => false
      | _ => true
    end.
  Instance is_prop_m : Proper (_eq ==> @Logic.eq bool) is_prop.
  Proof.
    intros [l lwf] [l' lwf'] H; compute in H; subst; simpl.
    unfold is_prop; reflexivity.
  Qed.
  Definition assumed (e : t) : F.lset :=
    filter is_prop (env e) ++
    (List.fold_right
      (fun i acc => {input_to_lit i; acc}) {} (CC.assumed (cc e))).
  Notation "'dom' t" := (assumed t) (at level 0).
  Notation "e |= l" := (query l e = true) 
    (no associativity, at level 24).

  Property assumed_empty : assumed empty [=] singleton L.ltrue.
  Proof.
    unfold assumed; simpl cc; rewrite CC.Specs.assumed_empty; simpl.
    set_iff; intuition.
  Qed.

  Lemma assumed_oapply :
    forall i e e', oapply (CC.assume i) e = Normal e' -> 
      assumed e' [=] {input_to_lit i; assumed e}.
  Proof.
    intros; destruct e; simpl in *;
      case_eq (CC.assume i cc0); intros; rewrite H0 in H;
        inversion_clear H.
    unfold assumed; simpl; rewrite (CC.Specs.assumed_assume H0); simpl.
    rewrite union_sym, union_add.
    apply add_m; try reflexivity.
    apply union_sym.
  Qed.
  Lemma filter_elim :
    forall l e, is_prop l = true -> 
      filter is_prop {l; e} [=] {l; filter is_prop e}.
  Proof.
    intros; intro a; set_iff.
    rewrite !filter_iff; eauto with typeclass_instances.
    set_iff; intuition.
    rewrite <- H1; exact H.
  Qed.
  Ltac case_Normal :=
    match goal with
      | |- (if ?X then Inconsistent else _) = _ -> _ =>
        destruct X; intro H; inversion_clear H; 
          unfold assumed; simpl; 
            rewrite filter_elim by reflexivity; apply union_add
    end.

  Property assumed_assume : forall e l E, 
    assume l e = Normal E -> assumed E [=] {l; assumed e}.
  Proof.
    intros [e c] [l lwf] E; destruct l; unfold assume; simpl.
    (* Proxy *)
    case_Normal.
    destruct l as [o b]; destruct o; [destruct a |].
    (* Atom *)
    case_Normal.
    (* Equation *)
    destruct b.
    case_eq (CC.assume (Equation u v) c); intros;
      inversion_clear H0; unfold assumed; simpl;
        rewrite (CC.Specs.assumed_assume H); simpl.
    rewrite union_sym, union_add.
    apply add_m; try reflexivity; apply union_sym.
    case_eq (CC.assume (Disequation u v) c); intros;
      inversion_clear H0; unfold assumed; simpl;
        rewrite (CC.Specs.assumed_assume H); simpl.
    rewrite union_sym, union_add.
    apply add_m; try reflexivity; apply union_sym.
    (* True/False *)
    case_Normal.
  Qed.

  Property  assumed_inconsistent : forall e l,
    assume l e = Inconsistent -> e |= L.mk_not l.
  Proof.
    intros e [l lwf]; destruct l.
    (* Proxy *)
    unfold assume, query; simpl.
    destruct (mk_not (mk_literal (RAW.Proxy pos neg) lwf) \in env e);
      try discr; auto.
    destruct l; destruct o; [destruct a|].
    (* Atom *)
    unfold assume, query; simpl.
    destruct (mk_not (mk_literal (RAW.Lit (Some (LITINDEX.Atom a), b))
      lwf) \in env e); try discr; auto.
    (* Equation *)
    destruct b; unfold assume, query; simpl; destruct e as [e c]; simpl.
    assert (H := @CC.Specs.assumed_inconsistent c (Equation u v)).
    destruct (CC.assume (Equation u v) c); intro; try discriminate.
    exact (H (refl_equal _)).
    assert (H := @CC.Specs.assumed_inconsistent c (Disequation u v)).
    destruct (CC.assume (Disequation u v) c); intro; try discriminate.
    exact (H (refl_equal _)).
    (* True/False *)
    unfold assume, query; simpl.
    destruct (mk_not (mk_literal (RAW.Lit (None, b))
      lwf) \in env e); try discr; auto.
  Qed.

  Property query_m : 
    Proper (_eq ==> @Logic.eq t ==> @Logic.eq bool) query.
  Proof.
    repeat intro; subst; destruct x; destruct y; simpl.
    compute in H; subst.
    unfold query; simpl.
    destruct this1; [|destruct l; destruct o; [destruct a|]].
    apply mem_m; auto; reflexivity.
    apply mem_m; auto; reflexivity.
    reflexivity.
    apply mem_m; auto; reflexivity.
  Qed.

  Import Sem.
  Implicit Type e : t.
  Implicit Type l : LLAZY.t.
  Lemma input_to_lit_lift :
    forall li i, List.In i li -> 
      (input_to_lit i) \In 
      fold_right (fun (i : input) (acc : lset) => {input_to_lit i; acc}) 
      {} li.
  Proof.
    induction li; intros i H; inversion_clear H; subst.
    apply add_1; reflexivity.
    apply add_2; auto.
  Qed.
  Corollary submodel_eq_submodel : 
    forall M e, Sem.submodel (dom e) M -> submodel_eq M (CC.assumed (cc e)).
  Proof.
    intros M [e c]; simpl.
    unfold SEMLAZY.submodel, assumed; simpl.
    generalize (CC.assumed c); induction l; intro H.
    constructor.
    destruct a; constructor.
    apply H; simpl; apply union_3; apply add_1; reflexivity.
    apply IHl; intros; apply H; simpl.
    rewrite union_sym, union_add; apply add_2; 
      rewrite union_sym; exact H0.
    apply H; simpl; apply union_3; apply add_1; reflexivity.
    apply IHl; intros; apply H; simpl.
    rewrite union_sym, union_add; apply add_2; 
      rewrite union_sym; exact H0.
  Qed.
  Property query_true : forall e l, e |= l ->
    (forall M, Sem.submodel (dom e) M -> (model_as_fun M) l).
  Proof.
    intros e [l lwf]; destruct l; unfold query; simpl; 
      intros Hquery M Hsub.
    apply Hsub; apply union_2;
      apply filter_3; [exact is_prop_m | exact (mem_2 Hquery) | reflexivity].
    destruct l; destruct o; [destruct a|].
    apply Hsub; apply union_2;
      apply filter_3; [exact is_prop_m | exact (mem_2 Hquery) | reflexivity].
    destruct b.
    rewrite (@Sem.morphism M _ (input_to_lit (Equation u v))) by reflexivity.
    apply CC.Specs.query_true with (cc e). exact Hquery.
    apply submodel_eq_submodel; assumption.
    rewrite (@Sem.morphism M _ 
      (input_to_lit (Disequation u v))) by reflexivity.
    apply CC.Specs.query_true with (cc e). exact Hquery.
    apply submodel_eq_submodel; assumption.
    apply Hsub; apply union_2;
      apply filter_3; [exact is_prop_m | exact (mem_2 Hquery) | reflexivity].
  Qed.

  Lemma in_cc_is_no_prop :
    forall l li, is_prop l = true -> 
      ~ (l \In fold_right (fun i acc => {input_to_lit i; acc}) {} li).
  Proof.
    intros l li H; induction li; simpl; intro abs.
    contradiction (empty_1 abs).
    rewrite add_iff in abs; destruct abs.
    rewrite <- H0 in H; destruct a; discriminate H.
    exact (IHli H0).
  Qed.
  Lemma lit_to_input_lift :
    forall li i, 
      (input_to_lit i) \In 
      fold_right (fun (i : input) (acc : lset) => {input_to_lit i; acc}) 
      {} li -> List.In i li.
  Proof.
    induction li; intros i H; simpl in H.
    contradiction (empty_1 H).
    rewrite add_iff in H; destruct H.
    left; destruct a; destruct i; compute in H; congruence.
    right; auto.
  Qed.
  Property query_assumed : forall e l, l \In dom e -> e |= l.
  Proof.
    intros e [l lwf]; unfold assumed, query; simpl;
      intro H; rewrite union_iff in H; destruct H as [H|H].
    (* the literal comes from the propositional environment *)
    destruct l; [|destruct l; destruct o; [destruct a |]].
    apply mem_1; apply filter_1 with is_prop; eauto with typeclass_instances.
    apply mem_1; apply filter_1 with is_prop; eauto with typeclass_instances.
    assert (Z := filter_2 H); discriminate Z.
    apply mem_1; apply filter_1 with is_prop; eauto with typeclass_instances.
    (* the literal comes from CC *)
    destruct l; [|destruct l; destruct o; [destruct a |]].
    refine (False_rect _ (in_cc_is_no_prop _ H)); reflexivity.
    refine (False_rect _ (in_cc_is_no_prop _ H)); reflexivity.
    destruct b.
    refine (@CC.Specs.query_assumed (cc e) (Equation u v) _).
    apply lit_to_input_lift; refine (In_1 _ H); reflexivity.
    refine (@CC.Specs.query_assumed (cc e) (Disequation u v) _).
    apply lit_to_input_lift; refine (In_1 _ H); reflexivity.
    refine (False_rect _ (in_cc_is_no_prop _ H)); reflexivity.
  Qed.

  Axiom query_monotonic :  (* juste pour pseudo-complétude du SAT *)
    forall e e' l, dom e [<=] dom e' -> e |= l -> e' |= l.

  Property query_expand : 
    forall e l, F.L.is_proxy l = true -> e |= l -> l \In dom e.
  Proof.
    intros e [l lwf] H; destruct l; try discriminate H.
    unfold query; simpl; intro A; apply union_2;
      apply filter_3; eauto with typeclass_instances; apply mem_2; auto.
  Qed.

(*   Axiom query_consistent :  *)
(*     forall e l, e |= l -> e |= L.mk_not l -> False. *)

  Hint Resolve query_monotonic query_assumed (* query_consistent *).
End ENVLAZY.
