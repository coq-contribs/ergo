(** This file provides an efficient proof search strategy
   for our derivation system defined in [Sat]. *)
Require Import Containers.Sets.
Require Import Env Sat.
Require Import SetoidList.
Require Import Arith.
Require Import FoldProps.

Fact belim : forall b, b = false -> b = true -> False.
Proof. congruence. Qed.

(** * The functor [SATSTRATEGY] *)
Module SATCAML 
  (Import CNF : Cnf.CNF)
  (Import E : ENV_INTERFACE CNF).

  (** We start by importing some efinitions from the SAT functor. *)
  Module Import S := SAT CNF E.
  Module SemF := S.SemF.
  Definition submodel_e G (M : Sem.model) := forall l, G |= l -> M l.
  Definition compatible_e G (D : cset) :=
    forall (M : Sem.model), submodel_e G M -> Sem.sat_goal M D.
  
  Notation "G |- D" := (mk_sequent G D) (at level 80).

  (** Relating lists of literals to clauses, and lists of lists of literals
     to sets of clauses (the reverse of [elements]). *)
  Fixpoint l2s (l : list L.t) : clause :=
    match l with
      | nil => {}
      | a::q => {a; l2s q}
    end.
  Fixpoint ll2s (l : list (list L.t)) : cset :=
    match l with
      | nil => {}
      | a::q => {l2s a; ll2s q}
    end.

  Property l2s_iff : forall l C, l \In l2s C <-> InA _eq l C.
  Proof.
    intros; induction C; simpl.
    intuition.
    split; simpl; intro H.
    rewrite add_iff in H; destruct H; intuition.
    rewrite add_iff; inversion H; intuition.
  Qed.

  Property ll2s_app : forall l l', ll2s (app l l') [=] ll2s l ++ ll2s l'.
  Proof.
    induction l; intros l'; simpl.
    intro k; set_iff; intuition.
    rewrite IHl, Props.union_add; reflexivity.
  Qed.
  Property ll2s_cfl : forall ll, cfl ll [=] ll2s ll.
  Proof.
    induction ll; rewrite cfl_1; simpl.
    reflexivity.
    apply add_m; auto. rewrite cfl_1 in IHll; exact IHll.
  Qed.
  Property l2s_Subset : 
    forall C C', (forall l, InA _eq l C -> InA _eq l C') <-> l2s C [<=] l2s C'.
  Proof.
    intros C C'; split; intros H k.
    rewrite !l2s_iff; auto.
    rewrite <- !l2s_iff; auto.
  Qed.

  Lemma ll2s_expand : forall (M : Sem.model) l, M l ->
    forall C, C \In ll2s (L.expand l) -> Sem.sat_clause M C.
  Proof.
    intros M l Hl C HC.
    assert (HM := Sem.wf_expand M l Hl).
    set (L := L.expand l) in *; clearbody L; clear l Hl.
    revert L HC HM; induction L; intros; simpl in  *.
    contradiction (empty_1 HC).
    rewrite add_iff in HC; destruct HC as [HC|HC].

    destruct (HM a (or_introl _ (refl_equal _))) as [k [Hk1 Hk2]].
    clear HM; exists k; split; auto.
    assert (Hk := ListIn_In Hk1); rewrite <- l2s_iff, HC in Hk; auto.   

    apply (IHL HC); intuition.
  Qed.
  
  (** Facts about measures of lists of (lists of) literals *)
  Property lsize_pos : forall l, l <> nil -> L.lsize l > 0.
  Proof.
    induction l; intros; simpl; auto.
    congruence.
    generalize (L.size_pos a); omega.
  Qed.
  Property llsize_app : 
    forall l l', L.llsize (app l l') = L.llsize l + L.llsize l'.
  Proof.
    induction l; simpl; intros; intuition.
    generalize (IHl l'); omega.
  Qed.

  (** ** Functions computing the BCP
     
     The following functions compute the proof search in a way that is similar
     to the OCaml procedure in [JFLA08]. We perform all possible binary 
     constraint propagation (BCP) before we start splitting on literals. *)

  (** The first function reduces a clause with respect to a partial 
     assignment. It returns [redNone] if the clause contains a literal
     that is true in the assignment, and the reduced clause in the 
     other case (with a flag telling if the function has changed anything). *)
  Section Reduce.
    Variable G : E.t.
    Variable D : cset.

    Inductive redRes : Type :=
    | redSome : list L.t -> bool -> redRes
    | redNone : redRes.

    Fixpoint reduce (C : list L.t) : redRes :=
      match C with
        | nil => redSome nil false
        | l::C' =>
          if query l G then redNone
            else
            match reduce C' with
              | redNone => redNone
              | redSome Cred b => 
                if query (L.mk_not l) G then
                  redSome Cred true
                  else redSome (l::Cred) b
            end
      end.

    Inductive reduce_spec_ (C : list L.t) : redRes -> Type :=
    | reduce_redSome : 
      forall Cred (bred : bool) 
        (HCred : Cred = List.filter (fun l => negb (query (L.mk_not l) G)) C)
        (Hsub : forall l, List.In l Cred -> query l G = false)
        (Hbred : if bred then L.lsize Cred < L.lsize C else C = Cred),
        reduce_spec_ C (redSome Cred bred)
    | reduce_redNone : 
      forall l (Hl : query l G = true) (Hin : List.In l C),
        reduce_spec_ C redNone.
    Theorem reduce_spec : forall C, reduce_spec_ C (reduce C).
    Proof.
      induction C; simpl.
      constructor; auto; intros; contradiction.
      case_eq (query a G); intro Hq.
      constructor 2 with a; intuition.
      destruct IHC; simpl.
      case_eq (query (L.mk_not a) G); intro Hnq.
      constructor; auto; simpl. 
      rewrite Hnq; simpl; auto.
      generalize (L.size_pos a); destruct bred; try rewrite Hbred; omega.
      constructor.
      simpl; rewrite Hnq; simpl; congruence.
      intros l Hl; inversion Hl; subst; eauto.
      destruct bred; try congruence; simpl; omega.
      constructor 2 with l; intuition.
    Qed.

    Corollary reduce_correct : forall C Cred bred,
      reduce C = redSome Cred bred -> derivable (G |- {l2s Cred; D}) -> 
      derivable (G |- {l2s C; D}).
    Proof.
      intros C Cred bred Hred Hder; 
        destruct (reduce_spec C); inversion Hred; subst.
      set (reds := filter (fun l : L.t => query (L.mk_not l) G) (l2s C)).
      assert (M : Proper (_eq ==> @eq bool) (fun l => query (L.mk_not l) G))
        by (eauto with typeclass_instances).
      apply ARed with reds (l2s C).

      unfold reds; intros k Hk; apply (filter_2 Hk).
      unfold reds; intros k Hk; apply (filter_1 Hk).
      apply add_1; auto.
      assert (E : l2s Cred [=] l2s C \ reds).
      rewrite <- H0; unfold reds; revert M; clear; intro M; induction C; simpl.
      intuition.
      case_eq (query (L.mk_not a) G); intro Ha; simpl.
      rewrite IHC, EProps.filter_add_1; auto.
      intro k; set_iff; intuition.
      apply H1; apply filter_3; auto; rewrite <- H2; assumption.
      rewrite IHC, EProps.filter_add_2; auto.
      intro k; set_iff; intuition.
      rewrite H0 in Ha; rewrite (filter_2 H) in Ha; discriminate.
      rewrite <- E; refine (weakening _ Hder _ _); split; simpl; intuition.
    Qed.
(*     Corollary reduce_complete : forall C Cred bred M, *)
(*       reduce C = redSome Cred bred ->  *)
(*       submodel_e G M -> Sem.sat_clause M (l2s C) -> Sem.sat_clause M (l2s Cred). *)
(*     Proof. *)
(*       intros C Cred bred M Hred Hsub;  *)
(*         destruct (reduce_spec C); inversion Hred; subst. *)
(*       intros [l Hsatl]; exists l; intuition. *)
(*       rewrite <- H0; revert H H1 Hsub; clear; induction C; simpl; auto; intros. *)
(*       rewrite add_iff in H1; destruct H1. *)
(*       case_eq (query (L.mk_not a) G); intro Hq; simpl. *)
(*       contradiction (SemF.model_em M l H). *)
(*       apply Hsub; rewrite <- H0; auto. *)
(*       apply add_1; auto. *)
(*       destruct (negb (query (L.mk_not a) G)); [apply add_2 |]; *)
(*         exact (IHC H H0 Hsub). *)
(*     Qed. *)
    Corollary reduce_complete : forall C Cred bred M,
      reduce C = redSome Cred bred -> 
      submodel_e G M -> Sem.sat_clause M (l2s Cred) -> 
      Sem.sat_clause M (l2s C).
    Proof.
      intros C Cred bred M Hred Hsub; 
        destruct (reduce_spec C); inversion Hred; subst.
      intros [l Hsatl]; exists l; intuition.
      rewrite <- H0 in H1; revert H H1 Hsub; clear; 
        induction C; simpl; auto; intros.
      destruct (query (L.mk_not a) G); simpl in *.
      apply add_2; apply IHC; auto.
      rewrite add_iff in H1; destruct H1; [apply add_1 | apply add_2]; auto.
    Qed.
 
  End Reduce.
  
  (** The second function simplifies a set of clauses  with respect 
     to a partial assignment. It returns [bcpNone] if one of the clauses
     reduced to the empty clause. Otherwise, it returns the set of
     simplified clauses along with a new partial assignment. Indeed,
     if simplification yields a unitary clause, [AAssume] is
     immediately applied and the literal is added to the partial
     assignment for the rest of the simplification. Again, we return
     a flag saying if the function has simplified anything or not.
     *)
  Section BCP.
    Inductive bcpRes : Type :=
    | bcpSome : E.t -> list (list L.t) -> bool -> bcpRes
    | bcpNone : bcpRes.

    Definition extend l s := app (L.expand l) s.
    Fixpoint bcp (G : E.t) (D : list (list L.t)) : bcpRes :=
      match D with
        | nil => bcpSome G nil false
        | C::D' =>
          match reduce G C with
            | redNone => 
              match bcp G D' with
                | bcpNone => bcpNone
                | bcpSome G' D' _ => bcpSome G' D' true
              end
            | redSome nil bred => bcpNone
            | redSome (l::nil) _ =>
              match assume l G with
                | Normal newG =>
                  match bcp newG D' with
                    | bcpNone => bcpNone
                    | bcpSome G' D' _ => bcpSome G' (extend l D') true
                  end
                | Inconsistent => bcpNone
              end
            | redSome Cred bred =>
              match bcp G D' with
                | bcpNone => bcpNone
                | bcpSome G' D' b =>
                  bcpSome G' (Cred::D') (bred || b)
              end
          end
      end.

    Lemma weak_assume : 
      forall (G : t) (D : cset) (l : L.t), 
        singleton l \In D -> ~ G |= l ->
        forall newG, assume l G = Normal newG ->
        derivable (newG |- cfl (L.expand l) ++ D) ->
        derivable (G |- D).
    Proof.
      intros G0 D0 l Hl HGl G1 Hass1 Hder.
      case_eq (query (L.mk_not l) G0); intro Hquery.
      (* - if [L.mk_not l] is entailed by [G0] then
         we can reduce [{l}] and apply [AConflict]. *)
      apply ARed with (reds:={l}) (C:={l}); intuition.
      rewrite <- (singleton_1 H); assumption.
      apply AConflict; apply add_1; intro k; set_iff; intuition.
      (* - otherwise, we first [AUnsat] with [l], the left branch
         is our hypothesis and we reduce and apply [AConflict] on
         the right. *)
      case_eq (assume (L.mk_not l) G0); [intros G2 Hass2 | intros Hass2].
      apply (AUnsat G0 D0 l G1 G2 Hass1 Hass2 Hder).
      apply ARed with (reds:={l}) (C:={l}).
      intro k; set_iff; intro Hk; apply query_assumed; 
        rewrite (assumed_assume Hass2); apply add_1; rewrite Hk; auto.
      reflexivity.
      apply union_3; auto.
      apply AConflict; apply add_1; intro k; set_iff; intuition.
      contradiction HGl; rewrite <- (L.mk_not_invol l);
        apply assumed_inconsistent; assumption.
    Qed.
      
    Theorem bcp_correct :
      forall D Dbasis G Gext Dred b,
        bcp G D = bcpSome Gext Dred b ->
        derivable (Gext |- ll2s Dred ++ Dbasis) ->
        derivable (G |- ll2s D ++ Dbasis).
    Proof with (eauto with typeclass_instances).
      intro D0; induction D0; intros Dbasis G0 Gext Dred b Hbcp Hder;
        simpl in Hbcp.
      inversion Hbcp; subst; simpl in Hder; inversion Hder; eauto with set.
      assert (Hred := reduce_correct G0 (ll2s D0 ++ Dbasis) a).
      assert (Hred' := reduce_spec G0 a).
      destruct (reduce G0 a) as [ared bred|].
      (* - if the reduction returned a clause (it can't be empty) *)
      destruct ared as [|l ared]; try discriminate.
      inversion Hred'; subst; destruct ared.
      (* - if it is a singleton [{l}], [l] is consistent with [G0] and
         we can apply [AAssume] *)
      assert (Hl' : ~ (G0 |= l)) by
        (intro abs; rewrite (Hsub l (or_introl _ (refl_equal _))) in abs; 
          discriminate).
      case_eq (assume l G0); [intros newG Hass | intros Hass];
        rewrite Hass in Hbcp.
      simpl; rewrite Props.union_add.
      apply (Hred (l::nil) bred (refl_equal _)); clear Hred.
      assert (IH := IHD0 (cfl (L.expand l) ++ Dbasis) newG); clear IHD0.
      destruct (bcp newG D0) as [Gext' Dred' b'|];
        try discriminate; inversion Hbcp.
      assert (IH' := IH Gext' Dred' b' (refl_equal _)); clear IH; subst.
      assert (Hl : Equal (l2s (l::nil)) {l})
        by (simpl; symmetry; apply Props.singleton_equal_add).
      destruct (In_dec (ll2s D0 ++ Dbasis) {l}).
      refine (weak_assume G0 _ l (add_1 _ _) Hl' _ Hass _)...
      rewrite Props.add_equal.
      2:(simpl; rewrite <- Props.singleton_equal_add; exact Htrue).
      rewrite <- Props.union_assoc.
      rewrite (Props.union_sym (cfl (L.expand l)) (ll2s D0)).
      rewrite Props.union_assoc; apply IH'.
      unfold extend in Hder; rewrite ll2s_app in Hder.
      rewrite ll2s_cfl, <- Props.union_assoc,
        (Props.union_sym (ll2s Dred')); exact Hder.
      refine (AAssume G0 _ l (add_1 _ _) _ Hass _)...
      rewrite Hl, Props.remove_add; auto.
      rewrite <- Props.union_assoc.
      rewrite (Props.union_sym (cfl (L.expand l)) (ll2s D0)).
      rewrite Props.union_assoc; apply IH'.
      unfold extend in Hder; rewrite ll2s_app in Hder.
      rewrite ll2s_cfl, <- Props.union_assoc,
        (Props.union_sym (ll2s Dred')); exact Hder.
      assert (Z : List.In l (l::nil)) by (left; auto).
      assert (Hnotl : ~ (G0 |= L.mk_not l)). 
      rewrite HCred, filter_In in Z; destruct (query (L.mk_not l) G0);
        auto; destruct Z; discriminate.
      contradiction (Hnotl (assumed_inconsistent Hass)).
      (* - if the reduced clause is not unitary *)
      simpl; rewrite Props.union_add.
      apply (Hred _ _ (refl_equal _)).
      set (Cred := l::t0::ared) in *; clearbody Cred.
      assert (IH := IHD0 {l2s Cred; Dbasis} G0); clear IHD0.
      destruct (bcp G0 D0) as [Gext' Dred' b'|];
        try discriminate; inversion Hbcp.
      assert (IH' := IH Gext' Dred' b' (refl_equal _)); clear IH; subst.
      rewrite Props.union_sym, <- Props.union_add, Props.union_sym.
      apply IH'. 
      rewrite Props.union_sym, Props.union_add, 
        Props.union_sym, <- Props.union_add; exact Hder.
      (* - if the clause was eliminated *)
      assert (IH := fun D => IHD0 D G0).
      destruct (bcp G0 D0); inversion Hbcp; subst.
      refine (weakening _ (IH _ _ _ _ (refl_equal _) Hder) _ _).
      split; simpl; try rewrite Props.union_add; intuition.
    Qed.

    Theorem bcp_unsat :
      forall D Dbasis G, bcp G D = bcpNone -> derivable (G |- ll2s D ++ Dbasis).
    Proof with (eauto with typeclass_instances).
      intro D0; induction D0; intros Dbasis G0 Hbcp; simpl in Hbcp.
      discriminate.
      assert (Hred := reduce_correct G0 (ll2s D0 ++ Dbasis) a).
      destruct (reduce_spec G0 a).
      (* - if the clause reduced to the empty clause, we apply [AConflict] *)
      simpl; rewrite Props.union_add.      
      destruct Cred as [|l Cred].
      apply (Hred nil bred (refl_equal _)).
      apply AConflict; apply add_1; reflexivity.
      destruct Cred.
      (* - if the clause is a singleton [{l}], [G0] must be
         consistent with [l] *)
      assert (Z : List.In l (l::nil)) by (left; auto).
      assert (Hnotl : ~ (G0 |= L.mk_not l)). 
      rewrite HCred, filter_In in Z; destruct (query (L.mk_not l) G0);
        auto; destruct Z; discriminate.
      assert (Hl' : ~ (G0 |= l)) by
        (intro abs; rewrite (Hsub l (or_introl _ (refl_equal _))) in abs; 
          discriminate).
      clear Z; apply (Hred (l::nil) bred (refl_equal _)).
      case_eq (assume l G0); [intros newG Hass | intros Hass];
        rewrite Hass in Hbcp.
      2:(contradiction (Hnotl (assumed_inconsistent Hass))).
      assert (IH := IHD0 (ll2s (L.expand l) ++ Dbasis) newG); 
        clear IHD0.
      destruct (bcp newG D0); try discriminate.
      simpl; rewrite <- Props.singleton_equal_add.
      assert (Hl : Equal (l2s (l::nil)) {l})
        by (simpl; symmetry; apply Props.singleton_equal_add).
      destruct (In_dec (ll2s D0 ++ Dbasis) {l}).
      refine (weak_assume G0 _ l (add_1 _ _) Hl' _ Hass _)...
      rewrite Props.add_equal; auto.
      rewrite <- Props.union_assoc.
      rewrite (Props.union_sym (cfl (L.expand l)) (ll2s D0)).
      rewrite Props.union_assoc, ll2s_cfl; exact (IH (refl_equal _)).
      refine (AAssume G0 _ l (add_1 _ _) _ Hass _)...
      rewrite Props.remove_add; auto.
      rewrite <- Props.union_assoc.
      rewrite (Props.union_sym (cfl (L.expand l)) (ll2s D0)).
      rewrite Props.union_assoc, ll2s_cfl; exact (IH (refl_equal _)).
      (* if the clause is not unitary after reduction *)
      assert (IH := IHD0 Dbasis G0); clear IHD0.
      destruct (bcp G0 D0); try discriminate.
      apply (Hred _ _ (refl_equal _)).
      refine (weakening _ (IH (refl_equal _)) _ _).
      split; simpl; intuition.
      (* if the clause was eliminated *)
      assert (IH := IHD0 Dbasis G0); clear IHD0.
      destruct (bcp G0 D0); try discriminate.
      refine (weakening _ (IH (refl_equal _)) _ _).
      split; simpl; intuition; rewrite Props.union_add; intuition.
    Qed.

    Theorem bcp_progress :
      forall D G Gext Dred b,
        bcp G D = bcpSome Gext Dred b -> 
        if b then L.llsize Dred < L.llsize D else Gext = G /\ Dred = D.
    Proof.
      intro D0; induction D0; intros G0 Gext Dred b Hbcp; simpl in Hbcp.
      inversion Hbcp; subst; split; reflexivity.
      destruct (reduce_spec G0 a).
      destruct Cred; try discriminate.
      destruct Cred.
      case_eq (assume t0 G0); [intros newG Hass | intros Hass];
        rewrite Hass in Hbcp; try discriminate.
      assert (IH := IHD0 newG).
      destruct (bcp newG D0); inversion Hbcp; subst.
      assert (IH' := IH _ _ _ (refl_equal _)); destruct b0.
      unfold extend; simpl; rewrite llsize_app.
      destruct bred; subst; simpl in *; generalize (L.size_expand t0); omega.
      destruct IH'; subst; unfold extend; simpl; rewrite llsize_app.
      destruct bred; subst; simpl in *; generalize (L.size_expand t0); omega.
      assert (IH := IHD0 G0).
      destruct (bcp G0 D0); inversion Hbcp; subst.
      destruct bred; simpl.
      assert (IH' := IH _ _ _ (refl_equal _)); destruct b0; simpl in *.
      omega. rewrite (proj2 IH'); omega.
      assert (IH' := IH _ _ _ (refl_equal _)); destruct b0; simpl in *.
      rewrite Hbred; simpl; omega.
      destruct IH'; split; congruence.
      assert (IH := IHD0 G0).
      destruct (bcp G0 D0); inversion Hbcp; subst.
      assert (IH' := IH _ _ _ (refl_equal _)); destruct b0; simpl.
      omega.
      rewrite (proj2 IH'); revert Hin; clear; induction a; simpl.
      contradiction. generalize (L.size_pos a); intuition.
    Qed.

    Theorem bcp_consistent :
      forall D G Gext Dred,
        bcp G D = bcpSome Gext Dred false -> 
        forall l C, C \In ll2s Dred -> l \In C -> 
          ~ Gext |= l /\ ~ Gext |= L.mk_not l.
    Proof.
      intros D0 G0 Gext Dred Hbcp l C HC Hl.
      assert (Hprog := bcp_progress D0 G0 _ _ _ Hbcp).
      destruct Hprog; subst.
      revert G0 l C Hl HC Hbcp; induction D0; intros; simpl in Hbcp.
      simpl in HC; contradiction (empty_1 HC).
      destruct (reduce_spec G0 a).
      destruct Cred; try discriminate.
      destruct Cred.
      case_eq (assume t0 G0); [intros newG Hass | intros Hass];
        rewrite Hass in Hbcp; try discriminate.
      destruct (bcp newG D0); discriminate.
      assert (IH := IHD0 G0 l); clear IHD0.
      destruct (bcp G0 D0); inversion Hbcp; subst.
      destruct bred; simpl in H3; try discriminate.
      set (Z := t0 :: t1 :: Cred) in *; clearbody Z.
      simpl in HC; rewrite add_iff in HC; destruct HC.
      rewrite <- H in Hl; rewrite l2s_iff in Hl.
      rewrite InA_alt in Hl; destruct Hl as [k [Hk1 Hk2]].
      split; intro abs.
      assert (Hk := Hsub k Hk2); rewrite <- Hk1 in Hk; congruence.
      rewrite HCred in Hk2; rewrite filter_In in Hk2.
      rewrite Hk1 in abs; destruct (query (L.mk_not k) G0); 
        destruct Hk2; discriminate.
      clear HCred; subst; eauto.
      destruct (bcp G0 D0); inversion Hbcp; subst.
    Qed.

    Lemma bcp_monotonic_env : 
      forall D G Gext Dred b,
        bcp G D = bcpSome Gext Dred b -> dom G [<=] dom Gext.
    Proof.
      intro D0; induction D0; intros G0 Gext Dred b Hbcp;
        simpl in Hbcp.
      inversion Hbcp; subst; simpl; reflexivity.
      destruct (reduce G0 a) as [Cred bred|].
      destruct Cred as [|l Cred]; try discriminate.
      destruct Cred.
      case_eq (assume l G0); [intros newG Hass | intros Hass];
        rewrite Hass in Hbcp; try discriminate.
      assert (IH := IHD0 newG).
      destruct (bcp newG D0); inversion Hbcp; subst.
      transitivity (dom newG).
      rewrite (assumed_assume Hass); intuition.
      exact (IH _ _ _ (refl_equal _)).
      assert (IH := IHD0 G0).
      destruct (bcp G0 D0); inversion Hbcp; subst.
      exact (IH _ _ _ (refl_equal _)).
      assert (IH := IHD0 G0).
      destruct (bcp G0 D0); inversion Hbcp; subst.
      exact (IH _ _ _ (refl_equal _)).
    Qed.

(*     Theorem bcp_complete :  *)
(*       forall D Dbasis G Gext Dred b, *)
(*         bcp G D = bcpSome Gext Dred b -> *)
(*         compatible_e G (ll2s D ++ Dbasis) ->  *)
(*         compatible_e Gext (ll2s Dred ++ Dbasis). *)
(*     Proof. *)
(*       intro D0; induction D0; intros Dbasis G0 Gext Dred b Hbcp Hsat; *)
(*         simpl in Hbcp. *)
(*       inversion Hbcp; subst; simpl; exact Hsat. *)
(*       assert (Hred := reduce_complete G0 a). *)
(*       destruct (reduce G0 a) as [Cred bred|]. *)
(*       destruct Cred as [|l Cred]; try discriminate. *)
(*       destruct Cred. *)
      
(*       assert (Hmon := bcp_monotonic_env D0 (assume l G0)). *)
(*       assert (IH := IHD0 (ll2s (L.expand l) ++ Dbasis) (assume l G0)); *)
(*         clear IHD0; destruct (bcp (assume l G0) D0); inversion Hbcp; subst. *)
(*       assert (IH' := IH _ _ _ (refl_equal _)); clear IH. *)
(*       intros M HM C HC; unfold extend in HC;  *)
(*         simpl in HC; rewrite ll2s_app in HC. *)
(*       rewrite (Props.union_sym _ (ll2s l0)), Props.union_assoc in HC. *)
(*       revert M HM C HC; apply IH'. *)
(*       intros M HM C HC; unfold extend in HC; simpl in HC;  *)
(*         rewrite (Props.union_sym (ll2s D0)),  Props.union_assoc in HC. *)
(*       rewrite union_iff in HC; destruct HC. *)
(*       apply ll2s_expand with l; auto; apply HM; apply EnvF.query_assume; auto. *)
(*       apply Hsat; auto. *)
(*       intros k Hk; apply HM; apply query_monotonic with G0; auto. *)
(*       rewrite assumed_assume; intuition. *)
(*       simpl; rewrite Props.union_add, Props.union_sym; apply add_2; auto. *)

(*       assert (Hmon := bcp_monotonic_env D0 G0). *)
(*       assert (IH := IHD0 Dbasis G0); *)
(*         clear IHD0; destruct (bcp G0 D0); inversion Hbcp; subst. *)
(*       assert (IH' := IH _ _ _ (refl_equal _)); clear IH. *)
(*       intros M HM C HC; simpl in HC; rewrite Props.union_add in HC. *)
(*       rewrite add_iff in HC; destruct HC. *)
(*       destruct (Hred _ _ M (refl_equal _)). *)
(*       intros k Hk; apply HM; apply query_monotonic with G0; auto; *)
(*         exact (Hmon _ _ _ (refl_equal _)). *)
(*       apply Hsat; [|simpl; apply union_2; apply add_1; auto]. *)
(*       intros k Hk; apply HM; apply query_monotonic with G0; auto; *)
(*         exact (Hmon _ _ _ (refl_equal _)). *)
(*       exists x; rewrite <- H; exact H0. *)
(*       apply IH'; auto; intros M' HM' C' HC'; apply Hsat; auto; *)
(*         simpl; rewrite Props.union_add; apply add_2; auto. *)

(*       assert (IH := IHD0 Dbasis G0); clear IHD0; destruct (bcp G0 D0); *)
(*         inversion Hbcp; subst. *)
(*       apply (IH Gext Dred b0 (refl_equal _)). *)
(*       intros M HM C HC; apply Hsat; auto. *)
(*       simpl; rewrite Props.union_add; apply add_2; exact HC. *)
(*     Qed. *)

    Theorem bcp_complete : 
      forall D Dbasis G Gext Dred b M,
        bcp G D = bcpSome Gext Dred b ->
        submodel_e Gext M -> Sem.sat_goal M (ll2s Dred ++ Dbasis) ->
        submodel_e G M /\ Sem.sat_goal M (ll2s D ++ Dbasis).
    Proof.
      intro D0; induction D0; intros Dbasis G0 Gext Dred b M Hbcp Hsub Hsat;
        simpl in Hbcp.
      inversion Hbcp; subst; simpl; tauto.
      assert (Hred := reduce_spec G0 a).
      assert (Hred' := reduce_complete G0 a).
      destruct (reduce G0 a) as [Cred bred|].
      destruct Cred as [|l Cred]; try discriminate.
      destruct Cred.

      case_eq (assume l G0); [intros newG Hass | intros Hass];
        rewrite Hass in Hbcp; try discriminate.
      assert (IH := IHD0 (ll2s (L.expand l) ++ Dbasis) newG); clear IHD0.
      destruct (bcp newG D0) as [Gext' Dred' b'|]; 
        inversion Hbcp; subst.
      destruct (IH Gext Dred' b' M) as [IH1 IH2]; auto.
      intros C HC; apply Hsat; simpl; unfold extend; 
        rewrite ll2s_app, (Props.union_sym _ (ll2s Dred')),
          Props.union_assoc; exact HC.
      split.
      intros k Hk; apply IH1; apply query_monotonic with G0; auto.
      rewrite (assumed_assume Hass); intuition.
      intros C HC; simpl in HC; rewrite Props.union_add, add_iff in HC; 
        destruct HC as [HC|HC].
      destruct (Hred' _ _ M (refl_equal _)) as [k [Hk1 Hk2]].
      intros k Hk; apply IH1; apply query_monotonic with G0; auto.
      rewrite (assumed_assume Hass); intuition.
      simpl; exists l; simpl; split; intuition.
      apply IH1; apply (EnvF.query_assume Hass); auto.
      exists k; rewrite <- HC; tauto.
      apply IH2; revert HC; set_iff; clear; tauto.

      assert (IH := IHD0 Dbasis G0); clear IHD0.
      destruct (bcp G0 D0) as [Gext' Dred' b'|]; inversion Hbcp; subst.
      destruct (IH Gext Dred' b' M) as [IH1 IH2]; auto.
      intros C HC; apply Hsat; simpl; rewrite Props.union_add;
        apply add_2; auto.
      split; auto; intros C HC; simpl in HC; 
        rewrite Props.union_add, add_iff in HC; 
          destruct HC as [HC|HC].
      destruct (Hred' _ _ _ (refl_equal _) IH1) as [k [Hk1 Hk2]].
      apply Hsat; simpl; apply union_2; apply add_1; auto.
      exists k; rewrite <- HC; tauto.
      auto.

      assert (IH := IHD0 Dbasis G0); clear IHD0.
      destruct (bcp G0 D0); inversion Hbcp; subst.
      destruct (IH Gext Dred b0 M) as [IH1 IH2]; auto.
      split; auto; intros C HC; simpl in HC; 
        rewrite Props.union_add, add_iff in HC; destruct HC as [HC|HC].
      inversion Hred; exists l; split.
      apply IH1; auto. rewrite <- HC, l2s_iff; exact (ListIn_In Hin).
      apply IH2; auto.
    Qed.
          
  End BCP.

  (** ** The main [proof_search] function *)
  (**  The [proof_search] function applies [bcp] repeatedly as long as 
     progress has been made, and otherwise just picks a literal to split on. *)
  Inductive Res : Type :=
  | Sat : E.t -> Res
  | Unsat.
  Fixpoint proof_search (G : E.t) (D : list (list L.t)) 
    (n : nat) {struct n} : Res :=
    match n with
      | O => Sat empty (* assert false *)
      | S n0 =>
        match bcp G D with 
          | bcpNone => Unsat
          | bcpSome newG newD b =>
            match newD with
              | nil => Sat newG
              | cons nil newD' => Unsat (* assert false *)
              | cons (cons l C) newD' =>
  (*   tant qu'on a progressé avec bcp, on reessaye *)
  (*   (si bcp etait recursive on n'aurait pas besoin de ça  *)
  (*    mais ca ne change rien en terme de performance ici) *)
                if b then proof_search newG newD n0
                else (* from that point on, G = newG, D = newD *)
                  match assume l G with
                    | Normal G1 =>
                      match proof_search G1 (extend l newD') n0 with
                        | Sat M => Sat M
                        | Unsat =>
                          let lbar := L.mk_not l in
                            match assume lbar G with
                              | Normal G2 =>
                                proof_search G2 (extend lbar (cons C newD')) n0
                              | Inconsistent => Unsat
                            end
                      end
                    | Inconsistent => Unsat
                  end
            end
        end
    end.

  Lemma expand_nonrec : 
    forall l C, C \In (cfl (L.expand l)) -> l \In C -> False.
  Proof.
    intros l C; rewrite cfl_1.
    assert (Hsize := L.size_expand l).
    revert Hsize; generalize (L.expand l); intro L; induction L;
      intros Hsize H Hl; simpl in *.
    contradiction (empty_1 H).
    rewrite add_iff in H; destruct H.
    set (N := L.llsize L) in *; clearbody N; clear L IHL.
    rewrite <- H in Hl; clear H C; induction a.
    simpl in Hl; contradiction (empty_1 Hl).
    simpl in Hl; rewrite add_iff in Hl; destruct Hl.
    simpl in Hsize; rewrite H in Hsize; omega.
    simpl in Hsize; apply IHa; auto; omega.
    apply IHL; auto.
    revert Hsize; clear; induction a; simpl; auto.
    intro; omega.
  Qed.
  Lemma expand_nonrec_2 : 
    forall l C, C \In (cfl (L.expand l)) -> L.mk_not l \In C -> False.
  Proof.
    intros l C; rewrite cfl_1.
    assert (Hsize := L.size_expand l).
    revert Hsize; generalize (L.expand l); intro L; induction L;
      intros Hsize H Hl; simpl in *.
    contradiction (empty_1 H).
    rewrite add_iff in H; destruct H.
    set (N := L.llsize L) in *; clearbody N; clear L IHL.
    rewrite <- H in Hl; clear H C; induction a.
    simpl in Hl; contradiction (empty_1 Hl).
    simpl in Hl; rewrite add_iff in Hl; destruct Hl.
    simpl in Hsize; rewrite H in Hsize; assert (Z := L.size_mk_not l); omega.
    simpl in Hsize; apply IHa; auto; omega.
    apply IHL; auto.
    revert Hsize; clear; induction a; simpl; auto.
    intro; omega.
  Qed.

  Property remove_transpose : forall (D : cset) (C C' : clause),
    {{D ~ C'} ~ C} [=] {{D ~ C} ~ C'}.
  Proof.
    intros; intro k; set_iff; intuition.
  Qed.
  Lemma remove_union : forall (D D' : cset) (C : clause), 
    ~C \In D -> {(D ++ D') ~ C} [=] D ++ {D' ~ C}.
  Proof.
    intros; intro k; set_iff; intuition.
    intro abs; rewrite abs in H; tauto.
  Qed.
  Lemma union_remove : forall (D D' : cset) (C : clause), 
    C \In D -> D ++ D' [=] D ++ {D' ~ C}.
  Proof.
    intros; intro k; set_iff; intuition.
    destruct (eq_dec C k); auto.
    rewrite H0 in H; left; auto.
  Qed.

(*   Lemma remove_singleton : forall l (A : clause),  *)
(*     singleton l \ A =/= singleton l -> singleton l \ A === {}. *)
(*   Proof. *)
(*     intros; intro k; split; set_iff; intuition. *)
(*     apply H; intro z; set_iff; intuition. *)
(*     rewrite <- H1 in H2; rewrite H0 in H2; tauto. *)
(*   Qed. *)
(*   Lemma diff_union : forall (A B C : clause), C \ (A ++ B) [=] C \ A \ B. *)
(*   Proof. *)
(*     intros; intro k; set_iff; intuition. *)
(*   Qed. *)
    
  Theorem proof_search_unsat :
    forall n G D, proof_search G D n = Unsat -> derivable (G |- ll2s D).
  Proof with (eauto with typeclass_instances).
    induction n; intros G0 D0; unfold proof_search.
    (* - if [D0] is empty, it is satisfiable *)
    intro abs; discriminate abs.
    (* - otherwise, we do a step of BCP *)
    fold proof_search; intro Hunsat.
    assert (Hbcp := bcp_correct D0 {} G0).
    assert (Hbcp2 := bcp_unsat D0 {} G0).
    assert (Hprogress := bcp_progress D0 G0).
    assert (Hcons := bcp_consistent D0 G0).
    destruct (bcp G0 D0) as [Gext Dred b|].
    (* -- if BCP returns a sequent, it can't be empty *)
    assert (Hbcp' := Hbcp Gext _ _ (refl_equal _)); clear Hbcp.
    rewrite !Props.empty_union_2 in Hbcp'; intuition.
    rewrite !Props.empty_union_2 in Hbcp2; intuition.
    (* -- if BCP returns a sequent, it can't be empty *)
    destruct Dred as [|C Dred]; try discriminate.
    destruct C as [|l C].
    (* -- if BCP returned a sequent with the empty clause, [AConflict] *)
    apply Hbcp'; simpl; apply AConflict; apply add_1; auto.
    destruct b; auto.
    (* -- if BCP didnt change anything... *)
    assert (Hcons' := Hcons Gext _ (refl_equal _)); clear Hcons.
    destruct (Hprogress _ _ _ (refl_equal _)); subst.
    simpl in Hcons'; destruct (Hcons' l {l; l2s C}) as [Hl Hnotl];
      try (simpl; apply add_1; reflexivity).
    case_eq (assume l G0); [intros G1 Hass1 | intros Hass1];
      rewrite Hass1 in Hunsat.
    2:(contradiction (Hnotl (assumed_inconsistent Hass1))).
    assert (IH1 := IHn G1 (extend l Dred)).
    (* -- the first recursive call must have return Unsat *)
    destruct (proof_search G1 (extend l Dred)); try discriminate.
    case_eq (assume (L.mk_not l) G0); [intros G2 Hass2 | intros Hass2];
      rewrite Hass2 in Hunsat.
    2:(rewrite <- (L.mk_not_invol l) in Hl;
      contradiction (Hl (assumed_inconsistent Hass2))).
    destruct (In_dec (ll2s Dred) (l2s (l :: C))).
    simpl; rewrite Props.add_equal; auto.
    apply AUnsat with l G1 G2; auto.
    unfold extend in IH1; rewrite ll2s_app in IH1.
    rewrite ll2s_cfl; exact (IH1 (refl_equal _)).
    destruct (In_dec (l2s C) l).
    simpl in Htrue; rewrite (Props.add_equal Htrue0) in Htrue.
    assert (IH2 := IHn _ _ Hunsat); unfold extend in IH2.
    rewrite ll2s_app in IH2; rewrite ll2s_cfl.
    simpl in IH2; rewrite (Props.add_equal Htrue) in IH2.
    exact IH2.
    apply ARed with {l} {l; l2s C}.
    intro k; set_iff; intro Hk; apply (EnvF.query_assume Hass2); 
      rewrite Hk; auto.
    intro k; set_iff; intuition.
    apply union_3; auto.
    assert (IH2 := IHn _ _ Hunsat); unfold extend in IH2.
    rewrite ll2s_app in IH2; rewrite ll2s_cfl.
    rewrite Props.union_sym, <- Props.union_add, Props.union_sym.
    rewrite <- Props.remove_diff_singleton, (Props.remove_add Hfalse).
    exact IH2.

    apply AUnsat with l G1 G2; auto.
    apply AElim with l (l2s (l::C)).
    apply query_assumed; rewrite (assumed_assume Hass1); apply add_1; auto.
    simpl; apply add_1; auto.
    apply union_3; simpl; apply add_1; auto.
    rewrite remove_union.
    2:(intro abs; apply expand_nonrec with l {l; l2s C}; intuition).
    simpl in Hfalse |- *; rewrite (Props.remove_add Hfalse).
    rewrite ll2s_cfl; unfold extend in IH1. 
    rewrite ll2s_app in IH1; exact (IH1 (refl_equal _)).
    assert (IH2 := IHn _ _ Hunsat).
    unfold extend in IH2; rewrite ll2s_app, <- ll2s_cfl in IH2; simpl in *.
    destruct (In_dec (l2s C) l).
    simpl in *; rewrite (Props.add_equal Htrue).
    exact IH2.
    apply AStrongRed with (C:=l2s (l::C))(reds := {l}).
    intro k; set_iff; intro Hk; apply (EnvF.query_assume Hass2); 
      rewrite Hk; auto.
    intro k; simpl; set_iff; intuition.
    apply union_3; simpl; apply add_1; auto.
    rewrite remove_union.
    2:(intro abs; apply expand_nonrec_2 
      with (L.mk_not l) {l; l2s C}; try rewrite L.mk_not_invol; intuition).
    simpl in Hfalse; rewrite (Props.remove_add Hfalse).
    rewrite Props.union_sym, <- Props.union_add, Props.union_sym.
    rewrite <- Props.remove_diff_singleton.
    rewrite (Props.remove_add Hfalse0).
    exact IH2.
    (* -- if BCP did not return a sequent, we apply the correctness of [bcp] *)
    rewrite Props.empty_union_2 in Hbcp2.
    exact (Hbcp2 (refl_equal _)).
    intuition.
  Qed.

  Theorem proof_search_sat :
    forall n G D M, L.llsize D < n ->
      proof_search G D n = Sat M -> 
      dom G [<=] dom M /\ compatible_e M (ll2s D).
  Proof.
    induction n; intros G0 D0 M Hlt; unfold proof_search.

    apply False_rec; omega.
    
    fold proof_search; intros Hsat.
    assert (Hbcp := bcp_complete D0 {} G0).
    assert (Hmon := bcp_monotonic_env D0 G0).
    assert (Hprogress := bcp_progress D0 G0).
    destruct (bcp G0 D0) as [Gext Dred b|]; try discriminate.
    destruct Dred as [|C Dred].

    inversion Hsat; subst; split.
    exact (Hmon _ _ _ (refl_equal _)).
    intros Model Hsub; destruct (Hbcp _ _ _ _ (refl_equal _) Hsub).
    intros k Hk; simpl in Hk.
    rewrite !Props.empty_union_2 in Hk; try solve [intuition].
    contradiction (empty_1 Hk).
    intros C HC; apply H0; apply union_2; auto.

    destruct C as [|l C]; try discriminate.
    assert (Hbcp' := fun Model => Hbcp _ _ _ Model (refl_equal _)); clear Hbcp.
    assert (Hprogress' := Hprogress _ _ _ (refl_equal _)); clear Hprogress.
    assert (Hmon' := Hmon _ _ _ (refl_equal _)); clear Hmon.
    destruct b; auto.
    
    destruct (IHn Gext ((l::C)::Dred) M) as [IH1 IH2]; auto; try omega.
    split. transitivity (dom (Gext)); auto.
    intros Model Hsub; destruct (Hbcp' Model) as [Hbcp1 Hbcp2].
    intros k Hk; apply Hsub; apply query_monotonic with Gext; auto.
    intros B HB; rewrite !Props.empty_union_2 in HB; try solve [intuition].
    apply IH2; auto.
    intros B HB; apply Hbcp2; apply union_2; auto.

    destruct Hprogress'; subst; clear Hmon' Hbcp'.
    case_eq (assume l G0) ; [intros G1 Hass1 | intros Hass1]; 
      rewrite Hass1 in Hsat; try discriminate.
    case_eq (proof_search G1 (extend l Dred) n);
      [intros M' Heq | intros Heq]; rewrite Heq in Hsat; simpl in Hsat.
    inversion Hsat; subst.
    destruct (IHn G1 (extend l Dred) M) as [IH1 IH2]; auto.
    unfold extend; simpl in *; rewrite llsize_app.
    generalize (L.size_expand l); omega.
    split.
    transitivity (dom G1); auto. rewrite (assumed_assume Hass1); intuition.
    simpl; intros Model Hsub B HB; rewrite add_iff in HB; destruct HB.
    exists l; split; [|rewrite <- H; apply add_1; auto].
    apply Hsub; apply query_monotonic with G1; auto.
    apply (EnvF.query_assume Hass1); auto.
    apply IH2; auto; unfold extend; rewrite ll2s_app; apply union_3; auto.

    case_eq (assume (L.mk_not l) G0); [intros G2 Hass2 | intros Hass2]; 
      rewrite Hass2 in Hsat; try discriminate.    
    destruct (IHn G2 (extend (L.mk_not l) (C::Dred)) M) as [IH1 IH2]; auto.
    unfold extend; simpl in *; rewrite llsize_app; simpl.
    generalize (L.size_mk_not l) (L.size_expand (L.mk_not l)); omega.
    split.
    transitivity (dom G2); auto.
    rewrite (assumed_assume Hass2); intuition.
    simpl; intros Model Hsub B HB; rewrite add_iff in HB; destruct HB.
    destruct (IH2 _ Hsub (l2s C)) as [k [Hk1 Hk2]].
    unfold extend; rewrite ll2s_app; apply union_3; apply add_1; auto.
    exists k; split; auto; rewrite <- H; apply add_2; auto.
    apply IH2; auto; unfold extend; rewrite ll2s_app; 
      apply union_3; apply add_2; auto.
  Qed.

  (** ** The main entry point to the SAT-solver *)
  Definition dpll (Pb : formula) :=
    let D0 := make Pb in
    let D0_as_list := List.map elements (elements D0) in
    let mu := (Datatypes.S (L.llsize D0_as_list)) in
      proof_search empty D0_as_list mu.

  Remark l2s_elements : forall C, l2s (elements C) [=] C.
  Proof.
    intros C k; rewrite (elements_iff C).
    remember (elements C) as L; clear C HeqL; revert k; induction L.
    simpl; split; intuition.
    intros k; split; intuition.
    simpl in H; rewrite add_iff in H; destruct H.
    constructor 1; auto.
    constructor 2; exact ((proj1 (IHL k)) H).
    inversion H; subst.
    apply add_1; auto.
    apply add_2; exact ((proj2 (IHL k)) H1).
  Qed.
  Remark ll2s_map_elements : 
    forall D, ll2s (List.map elements (elements D)) [=] D.
  Proof.
    intros D0 k; rewrite (elements_iff D0).
    remember (elements D0) as L; clear HeqL; revert D0 k; induction L.
    simpl; split; intuition.
    intros D0 k; split; intuition.
    simpl in H; rewrite add_iff in H; destruct H.
    constructor 1. rewrite l2s_elements in H; symmetry; auto.
    constructor 2; exact ((proj1 (H0 k)) H).
    simpl; inversion H; subst.
    apply add_1; rewrite l2s_elements; symmetry; auto.
    apply add_2; exact ((proj2 (H0 k)) H2).
  Qed.

  Theorem dpll_correct :
    forall Pb, dpll Pb = Unsat -> Sem.incompatible {} (make Pb).
  Proof.
    intros Pb Hunsat; unfold dpll in Hunsat.
    intros M HM; apply (soundness (empty |- make Pb)).
    assert (H := proof_search_unsat _ _ _ Hunsat).
    rewrite ll2s_map_elements in H; assumption.
    simpl; intros l; rewrite assumed_empty; set_iff; intro Hl.
    rewrite <- (Sem.morphism _ _ _ Hl); apply Sem.wf_true.
  Qed.

End SATCAML.
