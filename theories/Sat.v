(** This file is the backbone of our development. It contains
   the definition of the DPLL procedure, the proofs of its soundness
   and completeness. It also contains a naive but functional 
   proof search function that implements our DPLL system. 
*)

Require Import Arith Bool List.
Require Import DoubleNegUtils Cnf.
Require Import Semantics Env.
Require SetProperties. Module Props := SetProperties.
Require SetEqProperties. Module EProps := SetEqProperties.

(** Cannot Require Import Omega because the notations for positive conflict
    with the { C ~ D } notation in sets. *)
Declare ML Module "omega_plugin".

(** * The main functor [SAT] *)
Module SAT (CNF : CNF)(Import E : ENV_INTERFACE CNF).
  (** The functor [SAT] is parameterized by a module of type [CNF].
     The procedure and functions will be defined on the literals
     and formulas brought by the [CNF] module.

     The functor starts by constructing a semantic interface for
     [CNF] and also some properties about sets and sets of sets 
     of literals. *)
(*   Declare Module Import E : ENV_INTERFACE CNF. *)
  Module EnvF := EnvFacts CNF E.
  Import CNF.
  Module SemF := SemFacts(L)(Sem).
  
  (** ** Definition of the proof derivation system *)
  (** A [sequent] is just the pairing of a partial assignment [G] 
     and a set of clauses [D] to be satisfied. It is denoted [G |- D]. *)
  Record sequent : Type := mk_sequent {
    G : E.t;
    D : cset
  }.
  Notation "G |- D" := (mk_sequent G D) (at level 80).

  (** A sequent [G |- D] is said to be [incompatible] if no model
     extending [G] is a model of [D]. *)
  Definition incompatible (S : sequent) : Prop :=
    Sem.incompatible (dom (G S)) (D S).

  (** Our proof system is formalized as a set of inference rules. We encode it
     as an inductive predicate on sequents. Each constructor corresponds
     to an inference rule. *)
  Inductive derivable : sequent -> Prop :=
  | AConflict : 
    forall G D (i : {} \In D), 
      derivable (G |- D)
  | AAssume : 
    forall G D l (i : (singleton l) \In D) newG
      (Hass : assume l G = Normal newG),
      derivable (newG |- (cfl (L.expand l)) ++ ({D ~ (singleton l)})) ->
      derivable (G |- D)
  | AElim :
    forall G D l C (e : G |= l) (i : l \In C) (i0 : C \In D),
      derivable (G |- {D ~ C}) -> 
      derivable (G |- D)
  | ARed :
    forall G D reds C
      (e: forall l, l \In reds -> G |= L.mk_not l)
      (s : reds [<=] C) (i : C \In D),
      derivable (G |- {(C \ reds); D}) ->
      derivable (G |- D)
  | AUnsat :
    forall G D l G1 G2
      (Hass1 : assume l G = Normal G1) 
      (Hass2 : assume (L.mk_not l) G = Normal G2),
      derivable (G1 |- (cfl (L.expand l)) ++ D) ->
      derivable (G2 |- (cfl (L.expand (L.mk_not l))) ++ D)->
      derivable (G |- D).

  (** ** Correctness of the inference rules *)
  (** The first thing we want to do is prove the soundness of our
     derivation system, ie. that if a sequent is derivable, then
     it is incompatible. *)

  (** We start by a couple of useful weakening and morphism properties
     about derivability. *)
  Section Weakening.

    Definition sub_sequent (S S' : sequent) : Prop :=
      G S = G S' /\ D S [<=] D S'.
  
    Lemma weakening : forall S, derivable S -> 
      forall S', sub_sequent S S' -> derivable S'.
    Proof.
      intros S Hder; induction Hder; intros S' H; intros; 
        destruct S'; destruct H; simpl in *; subst.
      constructor 1; exact (H0 _ i).
      constructor 2 with l newG; auto; apply IHHder.
      split; simpl; auto; intro a.
      set_iff; intuition.
      constructor 3 with (l := l) (C := C); intuition eauto.
      apply IHHder; split; auto; simpl; intro a;
        try (rewrite remove_iff); intuition.
      constructor 4 with (reds := reds) (C := C); intuition eauto.
      apply IHHder; split; auto; simpl; intro a; auto.
      do 2 (rewrite add_iff); intuition.
      constructor 5 with l G1 G2; auto; [apply IHHder1 | apply IHHder2];
        split; simpl; auto; intro a; try (set_iff; intuition);
          rewrite assumed_assume in H1 |- *;
            revert H1 H; clear; set_iff; intuition.
    Qed.
    
    Definition eq_Seq (S S' : sequent) :=
      G S = G S' /\ (D S) [=] (D S').
    
    Lemma derivable_m : forall S, derivable S ->
      forall S', eq_Seq S S' -> derivable S'.
    Proof.
      intros S HS S' Heq; apply (weakening S HS S').
      destruct Heq as [HG HD]; split;
        [rewrite HG | rewrite HD]; reflexivity.
    Qed.

    Instance eq_Seq_Equivalence : Equivalence eq_Seq.
    Proof.
      constructor.
      intro x; split; reflexivity.
      intros x y [H1 H2]; split; symmetry; auto.
      intros x y z [H1 H2] [H1' H2']; split; eapply transitivity; eauto.
    Qed.

    Global Instance eq_Seq_m (G0 : E.t) : 
      Proper (Equal ==> eq_Seq) (mk_sequent G0).
    Proof.
      intros d d' H; split; auto; reflexivity.
    Qed.
    
    Global Instance derivable_morphism : Proper (eq_Seq ==> iff) derivable.
    Proof.
      intros S S' H; destruct S; destruct S'; 
        simpl; split; intro Z; refine (derivable_m _ Z _ _); 
          auto; symmetry; auto.
    Qed.
  End Weakening.

  (** An Application of weakening : a strong version of reduction 
     where the subsumed clause is removed as well. *)
  Theorem AStrongRed : forall (G : t) (D : cset) (reds C : clause),
    (forall l : L.t, l \In reds -> G |= L.mk_not l) ->
    reds[<=]C ->
    C \In D -> derivable (G |- {C \ reds; {D ~ C}}) -> derivable (G |- D).
  Proof.
    intros.
    apply ARed with reds C; auto.
    refine (weakening _ H2 _ _); split; simpl; intuition.
  Qed.

  (** Soundness of expand function *)
  Lemma expand_models : 
    forall (M : Sem.model) (l : L.t), 
      M l -> Sem.sat_goal M (cfl (L.expand l)).
  Proof.
    intros M l Hl.
    assert (H := SemF.model_expand M l Hl).
    assert (R := cfl_1 (L.expand l)).
    revert H R; generalize (L.expand l); clear.
    intro l; generalize (cfl l).
    induction l; simpl; intros s H R c Hc.
    crewrite R Hc; contradiction (empty_1 Hc).
    crewrite R Hc; rewrite add_iff in Hc; destruct Hc.

    clear IHl; assert (Ha := H a (or_introl _ (refl_equal a))).
    clear H l; revert c H0 Ha; induction a; simpl; intros;
      destruct Ha as [x [Hx Hx']]; try contradiction.
    destruct Hx; subst.
    exists x; split; auto. rewrite <- H0; intuition.
    destruct (IHa _ (reflexivity _)) as [y [Hy Hy']].
    exists x; tauto.
    exists y; split; auto.
    rewrite <- H0; apply add_2; assumption.

    refine (IHl _ _ _ c H0).
    intuition. reflexivity.
  Qed.

  Lemma submodel_add :
    forall (M : Sem.model) (G G' : E.t) (l : L.t),
      assume l G = Normal G' -> 
      Sem.submodel (dom G) M -> M l -> Sem.submodel (dom G') M.
  Proof.
    intros M G0 G1 l Hass Hsub Hl l' Hl'.
    rewrite (assumed_assume Hass), add_iff in Hl'.
    destruct Hl'; [exact (SemF.model_m _ _ _ H Hl) | exact (Hsub l' H)].
  Qed.

  (** This theorem states the [soundness] of the derivation system. 
     It is proven by induction on the derivation of the sequent [S]. *)
  Theorem soundness : forall S : sequent, derivable S -> incompatible S.
  Proof with (auto with typeclass_instances).
    intros S p; induction p; unfold incompatible; unfold Sem.incompatible;
      simpl; unfold Sem.sat_goal; intros; intro abs.
    (** - AAxiom : the empty clause is not satisfiable *)
    destruct (abs {} i) as [x [_ Hx]].
    rewrite empty_iff in Hx; contradiction.
    (** - AAssume : the unitary clause would have to be satisfied *)
    destruct (abs {l} i) as [m [Hm1 Hm2]].
    assert (Hl : M l).
    exact (SemF.model_m M _ _ (symmetry (singleton_1 Hm2)) Hm1).
    refine (IHp M (submodel_add M G0 newG l Hass H Hl) _); simpl.
    intros C; simpl; set_iff; intros [HC|[HC _]].
    exact (expand_models M l Hl C HC).
    exact (abs C HC).
    (** - AElim : the removed clause is satisfiable anyway *)
    exact (IHp M H (fun C HC => abs C (remove_3 HC))).
    (** - ARed : the removed literal is false anyway *)
    apply (IHp M H); intro C'; 
      case_eq (equal C' (C \ reds)); intros Hd HC'.
    rewrite <- equal_iff in Hd.
    destruct (abs C i) as [x [Hx1 Hx2]]; exists x; rewrite Hd.
    refine (conj Hx1 (diff_3 Hx2 _))...
    intro absx; pose (Ml := query_true (e x absx) H).
    exact (SemF.model_em M x Hx1 Ml).
    refine (abs C' (add_3 _ HC'))...
    intro abs1; symmetry in abs1; 
      rewrite (equal_1 abs1) in Hd; discriminate.
    (** - AUnsat : in a model, [l] would have to be either true or false *)
    elim (dnc (M l)); intro Hl; destruct Hl as [Hl | Hl].
    refine (IHp1 M (submodel_add M G0 _ l Hass1 H Hl) (fun C HC => _)).
    simpl in HC; rewrite union_iff in HC; destruct HC; auto.
    exact (expand_models M l Hl C H0).
    elim (SemF.model_full M l); intro Hfull.
    refine (IHp2 M (submodel_add M G0 _ _ Hass2 H (Hfull Hl)) _).
    intro C; simpl; set_iff; intros [HC|HC]; auto.
    exact (expand_models M _ (Hfull Hl) C HC).
  Qed.

  (** ** A naive strategy for proof search *)
  (** Now we will prove the completeness of the derivation system
     by constructing a function that tries to build a derivation
     and showing that this function is correct and complete. *)

  (** During the proof search, we will use a certain number of predicates
     to find clauses that have some properties. Their definition follows, 
     with some useful lemmas (e.g. compatibility lemmas) *)
  Set Implicit Arguments. Unset Strict Implicit.
  Section Filtering.
    Variable G : E.t.
    Variable D : cset.

    Section Finding.
      Variable f : clause -> bool.
      Variable compatf : Proper (_eq ==> @eq bool) f.

      Definition select :=
        (fun c p =>
          match p with 
            | Some _ => p
            | None => if f c then Some c else None
          end).

      Definition find (D : cset) := fold select D None.
      
      Lemma find_1 : 
        forall D C, find D = Some C -> C \In D.
      Proof.
        intros D0 C0; unfold find; rewrite fold_1.
        rewrite elements_iff; revert C0.
        generalize (elements D0); clear D0; intro l; pattern l.
        apply rev_ind; simpl.
        intros C0 abs; inversion abs.
        intros x l0 IH; rewrite (fold_left_app); simpl.
        intro C0;
          match goal with | |- select x ?F = _ -> _ => case_eq F end; intros.
        unfold select in H0; inversion H0; subst. 
        pose (IHH := IH C0 H); rewrite InA_alt in *; destruct IHH.
        exists x0; split; [exact (proj1 H1) | ].
        rewrite In_rev; rewrite rev_unit; simpl; right. 
        rewrite In_rev; rewrite rev_involutive; exact (proj2 H1).
        unfold select in H0; destruct (f x); inversion H0.
        apply In_InA; auto using Equal_pw_Equivalence with *. 
      Qed.
            
      Lemma find_2 : forall D C, find D = Some C -> f C = true.
      Proof.
        intros D0 C0; unfold find; rewrite fold_1;
          generalize C0; generalize (elements D0); 
            clear D0; clear C0; intro l; pattern l.
        apply rev_ind; simpl.
        intros C0  abs; discriminate.
        intros x l0 IH; rewrite (fold_left_app); simpl.
        intro C;
          match goal with | |- select x ?F = _ -> _ => case_eq F end; intros.
        unfold select in H0; inversion H0; subst; exact (IH _ H).
        simpl in H0; case_eq (f x); intro eq; rewrite eq in H0.
        inversion H0; subst; assumption.
        discriminate.
      Qed.

      Lemma find_3 : 
        forall D, find D = None -> forall C, C \In D -> f C = false.
      Proof.
        intros D0; unfold find; rewrite fold_1.
        intros IH C; rewrite elements_iff; revert C; revert IH.
        generalize (elements D0); clear D0; intro l; pattern l.
        apply rev_ind; simpl.
        intros _ C0 abs; inversion abs.
        intros x l0 IH; rewrite (fold_left_app); simpl.
        match goal with | |- select x ?F = _ -> _ => case_eq F end; intros.
        unfold select in IH0; inversion H0; discriminate.
        destruct (InA_app H0); [exact (IH H C H1) |].
        unfold select in IH0; case_eq (f x); intros.
        rewrite H2 in IH0; discriminate.
        inversion H1; [| inversion H4].
        rewrite H4; assumption.
      Qed.

    End Finding.
    
    (** - [is_empty] is compatible : it is already in SetFacts. *)

    (** - [eliminable C] filters clauses that contain a true atom *)
    Definition eliminable (c : clause) := exists_ (fun l : L.t => query l G) c.
    Global Instance compat_mem : 
      Proper (_eq ==> @eq bool) (fun l : L.t => query l G).
    Proof.
      repeat intro; rewrite H; auto.
    Qed.
    Global Instance compat_elim : Proper (_eq ==> @eq bool) eliminable.
    Proof.
      repeat intro; unfold eliminable.
      do 2 rewrite (EProps.exists_filter (f:=_)).
      rewrite H; reflexivity.
    Qed.

    (** - [reducible C] finds clauses that contain a false atom *)
    Definition reducible (c : clause) := 
      exists_ (fun l : L.t => query (L.mk_not l) G) c. 
    Global Instance compat_mem2 : 
      Proper (_eq ==> @eq bool) (fun l : L.t => query (L.mk_not l) G).
    Proof.
      repeat intro; rewrite H; auto.
    Qed.
    Global Instance compat_red : Proper (_eq ==> @eq bool) reducible.
    Proof.
      repeat intro; unfold reducible.
      do 2 rewrite (EProps.exists_filter (f:=_)).
      rewrite H; reflexivity.
    Qed.

    (** - other interesting clauses are unitary clauses, ie singletons.
       [unitary] filters those clauses. *)
    Definition unitary (C : clause) := 
      match choose C with 
        | Some x => is_empty {C ~ x}
        | _ => false 
      end.
    Global Instance compat_unitary : Proper (_eq ==> @eq bool) unitary.
    Proof.
      repeat intro; unfold unitary. 
      case_eq (choose x); intros; case_eq (choose y); intros.
      assert (Hx := choose_1 H0); clear H0.
      assert (Hy := choose_1 H1); clear H1.
      rewrite H in Hx |- *; destruct (eq_dec t0 t1) as [E|N].
      rewrite E; reflexivity.
      transitivity false; [|symmetry]; apply not_true_is_false; 
        rewrite <- is_empty_iff; intro A.
      apply A with t1; set_iff; intuition.
      apply A with t0; set_iff; intuition symmetry; auto.
      assert (Hx := choose_1 H0).
      assert (Hy := choose_2 H1).
      rewrite H in Hx; contradiction (Hy t0 Hx).
      assert (Hx := choose_1 H1).
      assert (Hy := choose_2 H0).
      rewrite H in Hy; contradiction (Hy t0 Hx).
      reflexivity.
    Qed.

    (** A unitary clause containing [l] is the singleton [l]. *)
    Lemma unitary_singl : forall C l, 
      unitary C = true -> l \In C -> C [=] singleton l.
    Proof.
      unfold Equal; unfold unitary; intros C l Hunit HC a.
      rewrite singleton_iff in *; split; intro H.
      case_eq (choose C); [intros z Hz | intro Hz]; rewrite Hz in Hunit.
      rewrite <- is_empty_iff in Hunit.
      destruct (eq_dec l a); auto.
      assert (Hz' := choose_1 Hz).
      destruct (eq_dec l z) as [e|n]. rewrite e in *.
      contradiction (Hunit a); set_iff; intuition.
      contradiction (Hunit l); set_iff; intuition (symmetry; auto).
      discriminate.
      rewrite H in HC; auto.
    Qed.
  
  End Filtering.
  Unset Implicit Arguments.
  Implicit Arguments find_3 [[compatf] D C].
    
  (** A context should be a valid partial model, the following 
     property expresses what this means in practice. *)
  Definition wf_context (G : lset) : Prop :=
    forall l, l \In G -> (L.mk_not l) \In G -> False.

  (** The result of our proof search will be either [Sat M] where [M]
     is a partial assignment satisfying the problem, or [Unsat] if
     no assignment has been found. *)
  Inductive Res : Type :=
    Sat : E.t -> Res
  | Unsat.

  (** The proof-search procedure takes a sequent as argument and
     tries to build a derivation for this sequent. It also takes an 
     extra integer argument which bounds the depth of recursive calls
     that the proof search can do. We will later show that we can find
     a measure such that we never reach that bound. 

     The proof search in itself consists in trying to apply one rule
     after the other as long as the set of clauses is not empty. Rules
     are tried in a sensible way : [AConflict], [AElim], [ARed], [AUnit]
     and finally [AUnsat] which splits on a literal.
  *)
  Fixpoint proof_search (S : sequent) (n : nat)
    {struct n} : Res :=
    match n with 
      | O => Sat empty (* assert false *)
      | S n0 => 
        if is_empty (D S) then Sat (G S)
        else 
          match find is_empty (D S) with
            | Some EC => Unsat
            | None =>
              match find (eliminable (G S)) (D S) with
                | Some C =>
                  proof_search ((G S) |- {(D S) ~ C}) n0
                | None =>
                  let reducers (C : clause) := 
                    filter (fun l => query (L.mk_not l) (G S)) C in
                    match find (reducible (G S)) (D S) with
                      | Some C =>
                        match choose (reducers C) with
                          | Some l =>
                            let Cred := C \ (singleton l) in
                              proof_search ((G S) |- {Cred; {D S ~ C}}) n0
                          | None => Sat empty (* assert false *)
                        end
                      | None => 
                        match find unitary (D S) with
                          | Some C => 
                            match choose C with
                              | Some l => 
                                match assume l (G S) with
                                  | Normal newG =>
                                    let D' := 
                                      (cfl (L.expand l)) ++
                                      (remove (singleton l) (D S)) in
                                      proof_search (newG |- D') n0
                                  | Inconsistent => Sat empty (* assert false *)
                                end
                              | None => Sat empty (* assert false *)
                            end
                          | None => 
                            match pick (D S) with
                              | Some (C, l) => 
                                match assume l (G S) with
                                  | Normal G1 =>
                                    match proof_search 
                                      (G1 |- remove C 
                                        (cfl (L.expand l) ++ D S)) n0 with
                                      | Sat M => Sat M
                                      | Unsat =>
                                        match assume (L.mk_not l) (G S) with
                                          | Normal G2 =>
                                            let Cred := C \ (singleton l) in
                                              proof_search 
                                              (G2 |- {Cred ; 
                                                {(cfl (L.expand (L.mk_not l)))
                                                  ++(D S) ~ C}}) 
                                              n0
                                          | Inconsistent =>
                                            Sat empty (* assert false *)
                                        end
                                    end
                                  | Inconsistent => Sat empty (* assert false *)
                                end
                              | None => Sat empty (* assert false *)
                            end
                        end
                    end
              end
          end
    end.
  
  (** ** Soundness and completeness proofs for the proof search *)
  (** The first proof we want about [proof_search] is its soundness with
     respect to our informal specification above, namely that it should not
     return [Unsat] unless it has found a derivation of the sequent. *)
  Theorem proof_search_unsat :
    forall n S, proof_search S n = Unsat -> derivable S.
  Proof.
    intro n; induction n; intro S; unfold proof_search.
    (** - Case n = 0 is absurd *)
    intro abs; discriminate abs.

    fold proof_search; destruct S; simpl in * |- *.
    case_eq (is_empty D0); intro empty_goal.
    (** - If the problem is empty... *)
    intro abs; discriminate abs.

    case_eq (find is_empty D0); [| intro empty_clause].
    (** - If there is an empty clause, we have a derivation *)
    intros C HC _; apply AConflict.
    assert (Cempty := find_2 HC).
    rewrite EProps.is_empty_equal_empty in Cempty.
    rewrite <- equal_iff in Cempty.
    rewrite <- Cempty; exact (find_1 HC).

    case_eq (find (eliminable G0) D0).
    (** - The next step is to try some BCP, first Elim ... *)
    intros C HC; pose (HC1 := find_1 HC); pose (HC2 := find_2 HC).
    destruct (EProps.exists_mem_4 (s:=C) HC2) as [l [HCl Hl]].
    intro IH; assert (IP := IHn _ IH).
    exact (AElim G0 D0 l C Hl (mem_2 HCl) HC1 IP).

    intro elim; case_eq (find (reducible G0) D0).
    (** - and then Red *)
    intros C HC; pose (HC1 := find_1 HC); pose (HC2 := find_2 HC).
    destruct (EProps.exists_mem_4 (s:=C) HC2) as [m [HCm Hm]].
    case_eq (choose (filter (fun l => query (L.mk_not l) G0) C)); [|intro abs].
    intros l Hl.
    assert (Hl1 := filter_1 (choose_1 Hl)).
    assert (Hl2 := filter_2 (choose_1 Hl)).
    simpl in Hl2; intro IH; assert (IP := IHn _ IH).
    apply (AStrongRed G0 D0 {l} C); auto.
    intros k Hk; assert (e := singleton_1 Hk);
      rewrite L.mk_not_compat in e; rewrite <- e; exact Hl2.
    intros k Hk; rewrite <- (singleton_1 Hk); exact Hl1.
    intro dis; discriminate dis.

    intro red; case_eq (find unitary D0).
    (** - When all possible BCP has been done, we turn to unitary clauses *)
    intros C HC; pose (HC1 := find_1 HC); pose (HC2 := find_2 HC).
    unfold unitary in HC2; case_eq (choose C).
    2:intro H; rewrite H in HC2; discriminate.
    intros l Hchoose; assert (Hl := unitary_singl HC2 (choose_1 Hchoose)).
    case_eq (assume l G0); [intros newG Hass | intros; discriminate].
    intro IH; pose (IP := IHn _ IH).
    apply (AAssume G0 D0 l) with newG; auto.
    rewrite <- Hl; exact HC1.

    (** - Now, our only alternative left is to pick any literal that
       appears in Delta and try it in an Unsat rule *)
    case_eq (pick D0). intros [C l] Hl.
    destruct (pick_1 _ _ _ Hl) as [Hpick1 Hpick2].
    (** -- we first use the IH on the left branch *)
    case_eq (assume l G0); [intros G1 Hass1 | intros; discriminate].
    intro unit; case_eq (proof_search 
      (G1 |- (remove C (union (cfl (L.expand l)) D0))) n);
    intro IH1.
    intros _ abs;  discriminate.
    (** -- and then on the second one *)
    case_eq (assume (L.mk_not l) G0); [intros G2 Hass2 | intros; discriminate].
    case_eq (proof_search (G2 |- (add (diff C (singleton l)) 
      (remove C (union (cfl (L.expand (L.mk_not l))) D0)))) n); intro IH2.
    intros _ abs; discriminate abs.
    intros _; refine (AUnsat G0 D0 l _ _ Hass1 Hass2 _ _).
    (** -- here we do more than one rule to ensure the measure decreases *)
    refine (AElim _ _ l C _ Hpick2 _ (IHn _ IH1)).
    apply (EnvF.query_assume Hass1); auto. apply union_3; exact Hpick1.
    refine (AStrongRed _ _ _ _ _ _ _ (IHn _ IH2)).
    intros k Hk; apply (EnvF.query_assume Hass2);
      rewrite <- L.mk_not_compat; exact (singleton_1 Hk).
    intros k Hk; exact (In_1 (singleton_1 Hk) Hpick2). 
    apply union_3; exact Hpick1.

    (** There remain cases where we were unable to pick a literal, but
       this means the problem is empty or all clauses are empty, which
       has already been treated before. *)
    intro abs; cut (Empty D0).
    intro P; rewrite (is_empty_iff) in P;
      rewrite P in empty_goal; discriminate.
    refine (pick_2 D0 (fun C HC Hemp => _) abs).
    rewrite (is_empty_iff) in Hemp.
    rewrite (find_3 is_empty empty_clause HC) in Hemp.
    discriminate.
  Qed.

  (** In order to prove the converse of this property, namely that 
     [proof_search] only returns [Sat _] if there is no derivation,
     we need a measure of sequents. *)
  Require Import Arith.
  Section Measure.
    
    (** The size of a sequent is the sum of the sizes of the literals
     that appear in the rhs of the sequent. *)
    Definition lsize l acc := L.size l + acc.
    Definition csize (C : clause) := fold lsize C.
    Definition size (S : sequent) := fold (A:=clause) csize (D S) 0.

    (** Quick facts about csize and 
       in order to be able to use results about fold *)
    Global Instance C_lsize : Proper (_eq ==> @eq nat ==> @eq nat) lsize.
    Proof.
      repeat intro; unfold lsize; subst.
      rewrite H; reflexivity.
    Qed.
    Fact T_lsize : transpose (eq (A:=nat)) lsize.
    Proof.
      unfold transpose; intros; unfold lsize; omega.
    Qed.

    Global Instance C_csize : Proper (_eq ==> @eq nat ==> @eq nat) csize.
    Proof.
      repeat intro; unfold csize; subst.
      apply (Props.fold_equal T_lsize _ H).
    Qed.
    Fact T_csize : transpose (eq (A:=nat)) csize.
    Proof.
      unfold transpose; unfold csize; intros.
      generalize T_lsize.
      generalize (fun l acc => L.size l + acc); intros f Hf.
      repeat rewrite fold_1; generalize (elements x).
      repeat rewrite fold_1; generalize (elements y).
      intro l; pattern l; apply rev_ind; intros l0; simpl.
      reflexivity.
      intros; do 2 rewrite fold_left_app; simpl; rewrite <- (H l2).
      clear x y H l; pattern l2; apply rev_ind; simpl.
      reflexivity.
      intros; do 2 rewrite fold_left_app; simpl.
      rewrite H; apply Hf.
    Qed.

    (** Straightforward properties about [lsize] *)
    Property lsize_monotonic : forall l acc1 acc2,
      acc1 <= acc2 -> lsize l acc1 <= lsize l acc2.
    Proof.
      intros; unfold lsize; omega.
    Qed.
    Property lsize_lt_compat : forall l acc1 acc2,
      acc1 < acc2 -> lsize l acc1 < lsize l acc2.
    Proof.
      intros; unfold lsize; omega.
    Qed.
    Property lsize_acc : forall l acc, acc <= lsize l acc.
    Proof.
      intros; unfold lsize; omega.
    Qed.
    
    (** A couple of properties about [csize] *)
    Property csize_acc : forall c acc, csize c acc = csize c 0 + acc.
    Proof.
      intros; unfold csize; do 2 rewrite fold_1.
      generalize (elements c) acc; clear.
      intro l; pattern l; apply rev_ind; intros; simpl.
      reflexivity.
      do 2 rewrite fold_left_app; rewrite H; 
        simpl; unfold lsize; omega.
    Qed.
    Property csize_monotonic : forall c acc1 acc2,
      acc1 <= acc2 -> csize c acc1 <= csize c acc2.
    Proof.
      intros; rewrite csize_acc; rewrite (csize_acc c acc2); omega.
    Qed.
    Property csize_lt_compat : forall c acc1 acc2,
      acc1 < acc2 -> csize c acc1 < csize c acc2.
    Proof.
      intros; rewrite csize_acc; rewrite (csize_acc c acc2); omega.
    Qed.
    Property csize_acc_ge : forall c acc, csize c acc >= acc.
    Proof.
      intros; rewrite csize_acc; omega.
    Qed.
      
    Property csize_in :
      forall c l acc, l \In c ->
        csize c acc = lsize l (csize {c ~ l} acc).
    Proof.
      intros; unfold csize.
      rewrite <- (Props.remove_fold_1 T_lsize acc H).
      reflexivity.
    Qed.

    (** Finally some similar properties about [size]. *)
    Property size_m : forall G G' D D', 
      D [=] D' -> size (G |- D) = size (G' |- D').
    Proof.
      intros G0 G1 D0 D1 Heq; unfold size; simpl in *.
      rewrite (Props.fold_equal T_csize 0 Heq).
      reflexivity.
    Qed.
    Property size_in :
      forall G D C, C \In D ->
        size (G |- D) = csize C 0 + size (G |- {D ~ C}).
    Proof.
      intros G0 D0 C HC; unfold size; simpl.
      rewrite <- (Props.remove_fold_1 T_csize 0 HC).
      generalize (fold csize (remove C D0) 0); intro n.
      unfold csize; do 2 rewrite fold_1; generalize (elements C).
      clear; intro l; revert n; pattern l; apply rev_ind; simpl.
      reflexivity.
      intros; repeat rewrite fold_left_app; simpl; unfold lsize in *.
      rewrite H; omega.
    Qed.
    Property size_add :
      forall G D C, ~C \In D -> size (G |- {C; D}) = csize C 0 + size (G |- D).
    Proof.
      intros G0 D0 C HC; unfold size; simpl.
      rewrite (Props.fold_add T_csize); auto.
      generalize (fold csize D0 0); intro n.
      unfold csize; do 2 rewrite fold_1; generalize (elements C).
      clear; intro l; revert n; pattern l; apply rev_ind; simpl.
      reflexivity.
      intros; repeat rewrite fold_left_app; simpl; unfold lsize in *.
      rewrite H; omega.
    Qed.
      
    (** [size] decreases when a clause is eliminated. *)
    Lemma size_elim_dec :
      forall G G' (D : cset) C l,
        C \In D -> l \In C -> size (G |- {D ~ C}) < size (G' |- D).
    Proof.
      intros G0 G1 D0 C l HC Hl; unfold size; simpl.
      rewrite <- (Props.remove_fold_1 T_csize 0 HC).
      generalize (fold csize {D0 ~ C} 0); intro n.
      rewrite (csize_in C l n Hl); unfold lsize.
      set (L.size_pos l); set (csize_acc (remove l C) n); omega.
    Qed.

    (** [size] decreases when a clause is reduced. *)
    Lemma size_red_dec :
      forall G D C l, C \In D -> l \In C ->
        size (G |- add (remove l C) (remove C D)) < size (G |- D).
    Proof.
      intros G0 D0 C l HC Hl; unfold size; simpl.
      case_eq (mem (remove l C) (remove C D0)); intro Hin.
      rewrite (Props.add_fold T_csize 0 (mem_2 Hin)).
      exact (size_elim_dec G0 G0 D0 C l HC Hl).
      rewrite (Props.fold_add T_csize).
      rewrite <- (Props.remove_fold_1 T_csize 0 HC).
      rewrite (csize_in C l _ Hl); set (L.size_pos l); unfold lsize; omega.
      intro abs; rewrite (mem_1 abs) in Hin; discriminate.
    Qed.

    (** Before we continue, two lemmas about size and expansion. *)
    Lemma size_union :
      forall G D D', size (G |- D ++ D') <= size (G |- D) + size (G |- D').
    Proof.
      intros G0 D0 D1; unfold size; simpl.
      revert D1; pattern D0; apply Props.set_induction; intros.
      rewrite (Props.fold_union T_csize).
      2:(intros x [absx _]; contradiction (H x absx)).
      generalize (fold csize D1 0); intro n.
      rewrite 2!fold_1; generalize (elements s); intro l.
      clear; pattern l; apply rev_ind; simpl; auto.
      intros; rewrite 2!fold_left_app; simpl.
      rewrite csize_acc. rewrite (csize_acc x (fold_left _ _ _)).
      omega.
      assert (R := (proj1 (Props.Add_Equal _ _ _) H1)).
      rewrite (Props.fold_equal T_csize 0 R).
      rewrite (Props.fold_add T_csize 0 H0).
      rewrite csize_acc.
      assert (Heq : (s' ++ D1) [=] (add x (s ++ D1))).
      rewrite R; apply Props.union_add.
      rewrite (Props.fold_equal T_csize 0 Heq).
      case_eq (mem x D1); intro Hmem.
      rewrite (Props.add_fold T_csize 0 (union_3 _ (mem_2 Hmem))).
      set (H D1); omega.
      rewrite (Props.fold_add T_csize 0).
      rewrite csize_acc; set (H D1); omega.
      intro abs; destruct (union_1 abs) as [a1|a2].
      contradiction (H0 a1).
      rewrite (mem_1 a2) in Hmem; discriminate.
    Qed.
    
    Lemma size_expand :
      forall l, fold csize (cfl (L.expand l)) 0 < L.size l.
    Proof.
      intros; assert (Hl := cfl_1 (L.expand l)).
      assert (Hsz : L.llsize (L.expand l) < L.size l).
      set (L.size_expand l); omega.
      rewrite (Props.fold_equal T_csize 0 Hl).
      refine (Arith.Lt.le_lt_trans _ _ _ _ Hsz).
      generalize (L.expand l); clear; induction l; simpl.
      rewrite Props.fold_1b; intuition.
      
      case_eq (mem (fold_right add {} a)
        (fold_right (fun (l0 : list L.t) (cl : cset) =>
          add (fold_right add {} l0) cl) {} l));
      intro Hmem.
      rewrite (Props.add_fold T_csize 0 (mem_2 Hmem)).
      refine (le_trans _ _ _ IHl _); clear.
      induction a; simpl; omega.
      rewrite (Props.fold_add T_csize 0).
      2:(intro abs; rewrite (mem_1 abs) in Hmem; discriminate).
      rewrite csize_acc; clear Hmem.
      cut (forall a b b' c, a + b <= c -> b' <= b -> a + b' <= c).
      2:intros; omega.
      intro cut; refine (cut _ _ _ _ _ IHl); clear.
      induction a; simpl; unfold csize in *.
      rewrite Props.fold_1b; intuition.
      case_eq (mem a (fold_right add ({} : clause) a0)); intro Hmem.
      rewrite (Props.add_fold T_lsize 0 (mem_2 Hmem)); omega.
      rewrite (Props.fold_add T_lsize 0).
      2:(intro abs; rewrite (mem_1 abs) in Hmem; discriminate).
      unfold lsize in *; omega.
    Qed.

    (** [size] decreases when a clause is assumed and expanded. *)
    Lemma size_assume_dec :
      forall G D l, In {l} D ->
        forall newG, assume l G = Normal newG ->
          size (newG |- cfl (L.expand l) ++ (remove {l} D))
          < size (G |- D).
    Proof.
      intros G0 D0 l HCl newG Hass; simpl.
      refine (Arith.Lt.le_lt_trans
        _ _ _ (size_union G0 _ _) _); unfold size; simpl.
      rewrite <- (Props.remove_fold_1 T_csize 0 HCl).
      assert (Hl : (singleton l : clause) [=] {l; {}}) by
        (exact (Props.singleton_equal_add l)).
      generalize (fold csize (remove (singleton l) D0) 0).
      intro n; rewrite Hl; unfold csize.
      rewrite (Props.fold_add T_lsize n).
      rewrite (Props.fold_empty); auto with typeclass_instances.
      apply plus_lt_compat_r; apply size_expand.
      intro abs; contradiction (empty_1 abs).
    Qed.

    (** [size] decreases when removing a clause that contains a literal
       and expanding a same-sized literal at the same time. *)
    Lemma size_left_unsat_dec :
      forall G G' D C l l', C \In D -> l \In C ->
        L.size l = L.size l' ->
        size (G' |- remove C (cfl (L.expand l') ++ D))
        < size (G |- D).
    Proof.
      intros G0 G1 D0 C l l' HC Hl Heq.
      apply plus_lt_reg_l with (csize C 0).
      rewrite <- (size_in G1 _ C (union_3 (cfl (L.expand l')) HC)).
      unfold size; simpl.
      refine (Arith.Lt.le_lt_trans
        _ _ _ (size_union G0 _ _) _); unfold size; simpl.
      set (size_expand l').
      set (csize_in _ _ 0 Hl); unfold lsize in e. omega.
    Qed.

    (** [size] decreases when reducing a clause by a literal and expanding
       a same-sized literal at the same time *)
    Lemma size_right_unsat_dec :
      forall G G' D C l l', C \In D -> l \In C ->
        L.size l = L.size l' ->
        let Cred := C \ (singleton l) in
          size (G |- {Cred; (remove C (cfl (L.expand l') ++ D))})
          < size (G' |- D).
    Proof.
      intros G0 G1 D0 C l l' HC Hl Heq.
      case_eq (mem (diff C {l})
        (remove C (cfl (L.expand l') ++ D0))); intro Hin.
      unfold size; simpl;
        rewrite (Props.add_fold T_csize 0 (mem_2 Hin)).
      exact (size_left_unsat_dec G0 G0 D0 C l l' HC Hl Heq).
      simpl; rewrite size_add.
      apply plus_lt_reg_l with (csize C 0); rewrite plus_permute.
      rewrite <- (size_in G0 _ _ (union_3 _ HC)).
      assert (Hu := size_union G0 (cfl (L.expand l')) D0); 
        unfold size in *; simpl in *.
      set (size_expand l').
      cut (csize (diff C {l}) 0+L.size l = csize C 0).
      intros; rewrite Heq in *; omega.
      revert Hl; clear; intro Hl.
      rewrite (csize_in _ _ _ Hl); unfold lsize; rewrite plus_comm.
      f_equal; apply C_csize; auto. 
      symmetry; exact (Props.remove_diff_singleton C l).
      intro abs; rewrite (mem_1 abs) in Hin; discriminate.
    Qed.
  
  End Measure.

  (** In addition to [wf_context], the current context and the 
     returned model must be consistent with literals' expansion.
     It is expressed in a different manner for the context and the
     counter model. *)
  Definition sat_clause_e (M : E.t) (C : clause) :=
    exists l, M |= l /\ l \In C.
  Definition sat_goal_e (M : E.t) (D : cset) :=
    forall C, C \In D -> sat_clause_e M C.

  Definition wf_expand (S : sequent) : Prop :=
    forall M, dom (G S) [<=] dom M -> sat_goal_e M (D S) ->
      forall l, G S |= l -> sat_goal_e M (cfl (L.expand l)).
  Definition model_expand (M : E.t) : Prop :=
    forall l, M |= l -> sat_goal_e M (cfl (L.expand l)).

  (** A quick lemma : [cfl (L.expand .)] is a morphism for literal equality *)
  Lemma cfl_expand_m : forall (l l' : L.t), 
      l === l' -> (cfl (L.expand l)) [=] (cfl (L.expand l')).
  Proof.
    intros l l' Heq.
    assert (Hleq := L.expand_compat l l' Heq).
    revert Hleq; generalize (L.expand l'); generalize (L.expand l).
    clear; induction l; intro l'; destruct l'; intro Hleq; inversion Hleq.
    reflexivity.
    subst; rewrite 2!cfl_1; simpl.
    assert (R := IHl l' H4); clear IHl.
    apply add_m.
    revert H2; clear; revert l0.
    induction a; intro a'; destruct a'; intro Hleq; inversion Hleq; simpl.
    reflexivity.
    subst; apply add_m. assumption. apply IHa; auto.
    rewrite 2!cfl_1 in R; exact R.
  Qed.

  (** We finally reach the wanted theorem about [proof_search]. 
     When it returns [Sat M], the proof search function should return a
     correct counter-model [M]. This proof also ensures that the abortion
     case (n=0) is never reached, ie. that our measure is adequate. This
     means that it is big enough at the start, and strictly decreases 
     at each recursive call. *)
  Theorem proof_search_sat :
    forall n S M, 
      size S < n -> wf_context (dom (G S)) -> wf_expand S ->
      proof_search S n = Sat M ->  
      wf_context (dom M) /\ model_expand M /\ 
      dom (G S) [<=] dom M /\ sat_goal_e M (D S).
  Proof with (eauto with typeclass_instances).
    intro n; induction n; intros S M Hm Hwf Hexp; unfold proof_search.
    (** - Case n = 0 is absurd *)
    contradiction (lt_n_O _ Hm).

    fold proof_search; destruct S; simpl in * |- *.
    case_eq (is_empty D0); intro empty_goal.
    (** - If the problem is empty, we have found a partial model *)
    rewrite <- is_empty_iff in empty_goal.
    intros X; inversion X; subst.
    refine (conj Hwf (conj _ (conj (fun x Hx => Hx) _))).
    refine (Hexp M (@Subset_refl _ _ _ _ (dom M)) _)...
    intros C HC; contradiction (empty_goal C HC).
    intros C HC; contradiction (empty_goal C HC).
    
    case_eq (find is_empty D0); [| intro empty_clause].
    intros; discriminate.
    case_eq (find (eliminable G0) D0).
    (** - The next step is to try some BCP, first Elim ... *)
    intros C HC; pose (HC1 := find_1 HC); pose (HC2 := find_2 HC).
    destruct (EProps.exists_mem_4 (s:=C) HC2) as [l [HCl Hl]].
    intro IH; destruct (IHn (G0 |- remove C D0) M) 
      as [Mwf [Mexp [Msub Msat]]].
    apply lt_S_n; refine (Arith.Lt.le_lt_trans _ _ _ (lt_le_S _ _ _) Hm).
    exact (size_elim_dec G0 G0 D0 C l HC1 (mem_2 HCl)).
    exact Hwf.
    intros m Hm1 Hm2; apply (Hexp m Hm1).
    intros C' HC'; case_eq (equal C C'); intro Heq.
    rewrite <- equal_iff in Heq.
    exists l; split; [exact (query_monotonic Hm1 Hl) |].
    rewrite <- Heq; exact (mem_2 HCl).
    refine (Hm2 C' (remove_2 _ HC'))...
    intro abs; rewrite (equal_1 abs) in Heq; discriminate.
    exact IH.
    refine (conj Mwf (conj Mexp (conj Msub _))).
    intros C' HC'; case_eq (equal C C'); intro Heq.
    rewrite <- equal_iff in Heq.
    exists l; split; [exact (query_monotonic Msub Hl) |].
    rewrite <- Heq; exact (mem_2 HCl).
    refine (Msat C' (remove_2 _ HC'))...
    intro abs; rewrite (equal_1 abs) in Heq; discriminate.

    intro elim; case_eq (find (reducible G0) D0).
    (** - and then Red *)
    intros C HC; pose (HC1 := find_1 HC); pose (HC2 := find_2 HC).
    destruct (EProps.exists_mem_4 (s:=C) HC2) as [k [HCk Hk]].
    case_eq (choose (filter (fun l => query (L.mk_not l) G0) C)); [|intro abs].
    intros l Hl.
    pose (Hl1 := filter_1 (choose_1 Hl)).
    pose (Hl2 := filter_2 (choose_1 Hl)).
    assert (Hrew := Props.remove_diff_singleton C l).
    2:(contradiction ((choose_2 abs) k 
      (filter_3 (H1:=compat_mem2 G0) (mem_2 HCk) Hk))).
    simpl in Hl2; intro IH; destruct (IHn (G0 |- add (diff C
      (singleton l)) (remove C D0)) M) as [Mwf [Mexp [Msub Msat]]].
    assert (Rew : {C \ singleton l; {D0 ~ C}} ===  {{C ~ l}; {D0 ~ C}}).
    rewrite Hrew; reflexivity.
    rewrite (size_m G0 G0 _ _ Rew).
    apply lt_S_n; refine (Arith.Lt.le_lt_trans _ _ _ (lt_le_S _ _ _) Hm).
    exact (size_red_dec G0 D0 C l HC1 Hl1).
    exact Hwf.
    intros m Hm1 Hm2; apply (Hexp m Hm1).
    intros C' HC'; case_eq (equal C C'); intro Heq.
    rewrite <- equal_iff in Heq.
    destruct (Hm2 {C ~ l}); try (apply add_1; symmetry; auto).
    exists x; split; [exact (proj1 H) |].
    rewrite <- Heq; exact (remove_3 (proj2 H)).
    refine (Hm2 C' (add_2 _ (remove_2 _ HC')))...
    intro abs; rewrite (equal_1 abs) in Heq; discriminate.
    exact IH.
    refine (conj Mwf (conj Mexp (conj Msub _))).
    intros C' HC'; case_eq (equal C C'); intro Heq.
    rewrite <- equal_iff in Heq.
    destruct (Msat {C ~ l}); try (apply add_1; symmetry; auto).
    exists x; split; [exact (proj1 H) |].
    rewrite <- Heq; exact (remove_3 (proj2 H)).
    refine (Msat C' (add_2 _ (remove_2 _ HC')))...
    intro abs; rewrite (equal_1 abs) in Heq; discriminate.
    
    (** Since we did all the BCP, we now know l and mk_not l are fresh for G
       as soon as l appears in D. This invariant guarantees that G will 
       remain well-formed. *)
    intro red.
    assert (fresh1 : forall C0 l, In C0 D0 -> In l C0 -> ~ G0 |= l).
    intros C0 l HC0 Hl abs; assert (abs1 : eliminable G0 C0 = true).
    unfold eliminable; refine (EProps.exists_mem_3 
      (s:=C0) (Comp := compat_mem G0) (mem_1 Hl) _)...
    rewrite (find_3 (eliminable G0) elim HC0) in abs1; discriminate.
    assert (fresh2 : forall C0 l,
      In C0 D0 -> In l C0 -> ~ G0 |= L.mk_not l).
    intros C0 l HC0 Hl abs; assert (abs2 : reducible G0 C0 = true).
    unfold eliminable; refine (EProps.exists_mem_3
      (s:=C0) (Comp := compat_mem2 G0) (mem_1 Hl) _)...
    rewrite (find_3 _ red HC0) in abs2; discriminate.
    assert (fresh_add1 : forall G1 C0 l, 
      In C0 D0 -> In l C0 -> assume l G0 = Normal G1 -> wf_context (dom G1)).
    intros G1 C0 l HC0 Hl Hass a Ha Hnota; simpl in * |-;
      rewrite (assumed_assume Hass), add_iff in Ha, Hnota.
    destruct Ha; destruct Hnota.
    rewrite H in H0; exact (L.mk_not_fix a H0).
    refine (fresh2 C0 a HC0 _ (query_assumed H0)). rewrite <- H; exact Hl.
    refine (fresh2 C0 (L.mk_not a) HC0 _ _).
    rewrite <- H0; exact Hl. 
    rewrite L.mk_not_invol; apply query_assumed; assumption.
    exact (Hwf a H H0).
    assert (fresh_add2 : forall G2 C0 l, 
      In C0 D0 -> In l C0 -> assume (L.mk_not l) G0 = Normal G2 -> 
      wf_context (dom G2)).
    intros G1 C0 l HC0 Hl Hass a Ha Hnota; simpl in * |-;
      rewrite (assumed_assume Hass), add_iff in Ha, Hnota.
    destruct Ha; destruct Hnota.
    rewrite H in H0; exact (L.mk_not_fix a H0).
    refine (fresh1 C0 (L.mk_not a) HC0 _ (query_assumed H0)).
    rewrite <- (L.mk_not_invol a) in H;
      rewrite <- (L.mk_not_compat l (L.mk_not a)) in H.
    rewrite <- H; exact Hl.
    rewrite <- (L.mk_not_compat l a) in H0; rewrite H0 in Hl.
    exact (fresh1 C0 a HC0 Hl (query_assumed H)).
    exact (Hwf a H H0).

    case_eq (find unitary D0); [|intro unit].
    (** - When all possible BCP has been done, we turn to unitary clauses *)
    intros C HC; pose (HC1 := find_1 HC); pose (HC2 := find_2 HC).
    unfold unitary in HC2; case_eq (choose C).
    2:(intro H; rewrite H in HC2; discriminate).
    intros l Hchoose; 
      pose (Hl := unitary_singl HC2 (choose_1 Hchoose)).
    assert (temp : In {l} D0) by (apply In_1 with C; auto).
    case_eq (assume l G0); [intros newG Hass | intro Hass].
    intro IH; destruct (IHn (newG |-
      (union (cfl (L.expand l)) (remove {l} D0))) M)
    as [Mwf [Mexp [Msub Msat]]].
    apply lt_S_n; refine (Arith.Lt.le_lt_trans _ _ _ (lt_le_S _ _ _) Hm).
    apply size_assume_dec; auto; exact temp.
    exact (fresh_add1 newG C l HC1 (choose_1 Hchoose) Hass).
    intros m Hm1 Hm2 k Hk; case_eq (L.is_proxy k); intro Hproxy.
    simpl in Hk; assert (Hk' := query_expand Hproxy Hk); 
      rewrite (assumed_assume Hass) in Hk'.
    destruct (eq_dec l k) as [e|n0].
    intros c' Hc'; apply Hm2; apply union_2.
    rewrite (cfl_expand_m l k e); assumption.
    apply (Hexp m).
    simpl in Hm1; rewrite (assumed_assume Hass) in Hm1.
    exact (fun l' Hl' => Hm1 l' (add_2 l Hl')).
    intros C' HC'; case_eq (equal (singleton l) C'); intro Heq.
    rewrite <- equal_iff in Heq.
    simpl in Hm1; rewrite (assumed_assume Hass) in Hm1.
    exists l; split; [exact (query_assumed
      (Hm1 l (add_1 (dom G0) (reflexivity l)))) |].
    rewrite <- Heq; exact (singleton_2 (reflexivity l)).
    refine (Hm2 C' (union_3 _ (remove_2 _ HC')))...
    intro abs; rewrite (equal_1 abs) in Heq; discriminate.
    apply query_assumed; apply add_3 with l; assumption.
    rewrite (L.is_proxy_nil _ Hproxy); intros C' HC'; 
      rewrite cfl_1 in HC'; simpl in HC'; contradiction (empty_1 HC').
    exact IH.
    refine (conj Mwf (conj Mexp (conj _ _ ))).
    simpl in Msub; rewrite (assumed_assume Hass) in Msub.
    exact (fun l' Hl' => Msub l' (add_2 l Hl')).
    intros C' HC'; case_eq (equal (singleton l) C'); intro Heq.
    rewrite <- equal_iff in Heq.
    exists l; split; 
      [exact (query_monotonic Msub
        (EnvF.query_assume Hass (reflexivity l))) |].
    rewrite <- Heq; exact (singleton_2 (reflexivity l)).
    refine (Msat C' (union_3 _ (remove_2 _ HC')))...
    intro abs; rewrite (equal_1 abs) in Heq; discriminate.
    contradiction (fresh2 {l} l); intuition.
    exact (assumed_inconsistent Hass).

    (** - Now, our only alternative left is to pick any literal that
       appears in Delta and try it in an Unsat rule *)
    case_eq (pick D0).
    intros [C0 l] Hpick; destruct (pick_1 D0 C0 l Hpick) as [HC0 Hl].
    (** -- we first use the IH on the left branch if it is Sat *)
    case_eq (assume l G0); [intros G1 Hass1 | intros Hass1].
    case_eq (proof_search (G1 |- 
      remove C0 (union (cfl (L.expand l)) D0)) n); intro M'.
    intros IH1 X; inversion X; subst.
    destruct (IHn (G1 |- remove C0 
      (union (cfl (L.expand l)) D0)) M) as [Mwf [Mexp [Msub Msat]]].
    apply lt_S_n; refine (Arith.Lt.le_lt_trans _ _ _ (lt_le_S _ _ _) Hm).
    apply size_left_unsat_dec with l; auto.
    exact (fresh_add1 G1 C0 l HC0 Hl Hass1).
    intros m Hm1 Hm2 k Hk; case_eq (L.is_proxy k); intro Hproxy.
    simpl in Hk; assert (Hk' := query_expand Hproxy Hk); 
      rewrite (assumed_assume Hass1) in Hk'.
    destruct (eq_dec l k) as [e|n0].
    intros c' Hc'; destruct (eq_dec C0 c') as [E|N].
    exists l; split. 
    apply (query_monotonic Hm1); apply (EnvF.query_assume Hass1); auto.
    rewrite <- E; auto.
    apply Hm2; apply remove_2; auto.
    apply union_2; rewrite (cfl_expand_m l k e); assumption.
    apply (Hexp m).
    simpl in Hm1; rewrite (assumed_assume Hass1) in Hm1.
    exact (fun l' Hl' => Hm1 l' (add_2 l Hl')).
    intros C HC; simpl in Hm1.
    destruct (eq_dec C0 C) as [E|N].
    exists l; split. 
    apply (query_monotonic Hm1); apply (EnvF.query_assume Hass1); auto.
    rewrite <- E; auto.
    apply Hm2; apply remove_2; auto. apply union_3; auto.
    simpl in Hm1; rewrite (assumed_assume Hass1) in Hm1.
    apply query_assumed; apply add_3 with l; assumption.
    rewrite (L.is_proxy_nil _ Hproxy); intros C' HC'; 
      rewrite cfl_1 in HC'; simpl in HC'; contradiction (empty_1 HC').
    exact IH1.
    simpl in Msub; rewrite (assumed_assume Hass1) in Msub.
    refine (conj Mwf (conj Mexp 
      (conj (fun l' Hl' => Msub l' (add_2 _ Hl')) _)))...
    intros C HC; simpl in Msat; revert HC Hl Msat Msub; clear; intros.
    destruct (eq_dec C0 C) as [E|N].
    exists l; split.
    apply query_assumed; apply Msub; apply add_1; auto.
    rewrite <- E; auto.
    apply Msat; apply remove_2; auto. apply union_3; auto.
    2:contradiction (fresh2 C0 l HC0 Hl (assumed_inconsistent Hass1)).
    
    (** -- and then we second one *)
    case_eq (assume (L.mk_not l) G0); [intros G2 Hass2 | intros Hass2].
    intros IH2; destruct (IHn (G2 |- add (diff C0 (singleton l))
      (remove C0 (union (cfl (L.expand (L.mk_not l))) D0))) M)
    as [Mwf [Mexp [Msub Msat]]].
    apply lt_S_n; refine (Arith.Lt.le_lt_trans _ _ _ (lt_le_S _ _ _) Hm).
    apply size_right_unsat_dec; auto; rewrite L.size_mk_not; trivial.
    exact (fresh_add2 G2 C0 l HC0 Hl Hass2).
    intros m Hm1 Hm2 k Hk; case_eq (L.is_proxy k); intro Hproxy.
    simpl in Hk; assert (Hk' := query_expand Hproxy Hk); 
      rewrite (assumed_assume Hass2) in Hk'.
    destruct (eq_dec (L.mk_not l) k).
    intros c' Hc'; destruct (eq_dec C0 c') as [E|N].
    destruct (Hm2 (diff C0 (singleton l))).
    apply add_1; reflexivity.
    exists x; intuition; rewrite <- E; exact (diff_1 H2).
    apply Hm2; apply add_2; apply remove_2; auto.
    apply union_2; rewrite (cfl_expand_m (L.mk_not l) k); assumption.
    apply (Hexp m).
    simpl in *; rewrite (assumed_assume Hass2) in Hm1.
    exact (fun l' Hl' => Hm1 l' (add_2 (L.mk_not l) Hl')).
    intros C HC; simpl in Hm2; revert HC Hl Hm2 Hm1; clear; intros.
    destruct (eq_dec C0 C) as [E|N].
    destruct (Hm2 (diff C0 (singleton l))); auto with set.
    apply add_1; auto.
    exists x; intuition; rewrite <- E; exact (diff_1 H1).
    apply Hm2; apply add_2; apply remove_2; auto.
    apply union_3; auto.
    apply query_assumed; apply add_3 with (L.mk_not l); assumption.
    rewrite (L.is_proxy_nil _ Hproxy); intros C' HC'; 
      rewrite cfl_1 in HC'; simpl in HC'; contradiction (empty_1 HC').
    exact IH2.
    simpl in Msub; rewrite (assumed_assume Hass2) in Msub.
    refine (conj Mwf (conj Mexp 
      (conj (fun l' Hl' => Msub l' (add_2 _ Hl')) _)))...
    intros C HC; simpl in Msat; revert HC Hl Msat Msub; clear; intros.
    destruct (eq_dec C0 C) as [E|N].
    destruct (Msat (diff C0 (singleton l))); auto with set.
    apply add_1; auto.
    exists x; intuition; rewrite <- E; exact (diff_1 H1).
    apply Msat; apply add_2; apply remove_2; auto. 
    apply union_3; auto.
    assert (Z := assumed_inconsistent Hass2).
    rewrite L.mk_not_invol in Z.
    contradiction (fresh1 C0 l HC0 Hl Z).

    (** There remain cases where we were unable to pick a literal, but
       this means the problem is empty or all clauses are empty, which
       has already been treated before. *)
    intro abs; cut (Empty D0).
    intro P; rewrite is_empty_iff in P;
      rewrite P in empty_goal; discriminate.
    refine (pick_2 D0 (fun C HC Hemp => _) abs).
    rewrite is_empty_iff in Hemp.
    rewrite (find_3 _ empty_clause HC) in Hemp.
    discriminate.
  Qed.

  (** ** The main entry point to the SAT-solver 
     
     We can now define a function that takes a [formula], builds
     a sequent with an empty partial assignment out of it, and 
     applies [proof_search] to try and find a derivation for this
     sequent. It uses our measure in order to pass a suitable
     bound at the start.
     This function [dpll] is correct as a consequence the correctness
     of [proof_search] and of the derivation system. It is a decision
     procedure for the satisfiability of [formula]s.
     *)
  Definition dpll (Pb : formula) :=
    let S := empty |- make Pb in
      let mu := Datatypes.S (size S) in
        proof_search S mu.
  Lemma dpll_correct :
    forall Pb, dpll Pb = Unsat -> Sem.incompatible {} (make Pb).
  Proof.
    intros Pb Hunsat; unfold dpll in Hunsat.
    intros M HM; apply (soundness (empty |- make Pb)).
    exact (proof_search_unsat _ _ Hunsat).
    simpl; intros l; rewrite assumed_empty; set_iff; intro Hl.
    rewrite <- (Sem.morphism _ _ _ Hl); apply Sem.wf_true.
  Qed.

(*   (** ** Completion *)
  
(*      Using the completion implemented in the [SemFacts], we can complete *)
(*      a partial model as returned by [proof_search] in a total model (due *)
(*      to expansion of literals, this is not a trivial proof, cf. [SemFacts]. *)
(*      Together with [dpll_correct], this means that [dpll] is a correct *)
(*      and complete decision procedure. *)
     
(*      Note that completeness is not used when using [dpll] to prove *)
(*      things by reflection. It is satsifactory nonetheless to be able *)
(*      to prove this completeness result. *) *)
(*   Fact wf_empty : wf_context (dom empty). *)
(*   Proof. *)
(*     unfold wf_context; intros l Hl Hnotl. *)
(*     apply (query_consistent (query_assumed Hl) (query_assumed Hnotl)). *)
(*   Qed. *)
(*   Fact wexp_empty : *)
(*     forall Pb, wf_expand (empty |- make Pb). *)
(*   Proof. *)
(*     intros Pb M Hm1 Hm2 l Hl; simpl in *. *)
(*     intros c Hc; rewrite cfl_1 in Hc; simpl in Hc. *)
(*     case_eq (L.is_proxy l); intro Hproxy. *)
(*     assert (Hl' := query_expand Hproxy Hl). *)
(*     rewrite assumed_empty, singleton_iff in Hl'. *)
(*     rewrite <- Hl', L.is_proxy_true in Hproxy; discriminate. *)
(*     rewrite (L.is_proxy_nil _ Hproxy) in Hc; simpl in Hc. *)
(*     contradiction (empty_1 Hc). *)
(*   Qed. *)

(*   (** We reformulate the constraint on M and expansion of literals *) *)
(*   Lemma model_expand_1 : *)
(*     forall M, model_expand M -> *)
(*       (forall l, M |= l -> *)
(*         (forall c, List.In c (L.expand l) -> *)
(*           exists y, List.In y c /\ M |= y)). *)
(*   Proof. *)
(*     intros M Mexp l Hl; generalize (Mexp l Hl); clear; unfold model_expand. *)
(*     generalize (L.expand l); clear; induction l; intro Hsat. *)
(*     intros c Hc; contradiction Hc. *)
(*     intros c [Ha|Hc]; subst; *)
(*       set (C := fold_right add ({} : clause) c); *)
(*         assert (Hsat'  := Hsat C); rewrite cfl_1 in Hsat'; simpl in Hsat'. *)
(*     fold C in Hsat'; destruct Hsat' as [x Hx]. apply add_1; auto. *)
(*     revert Hx; clear; induction c. *)
(*     simpl in C; unfold C; intros [_ abs]; *)
(*       contradiction (empty_1 abs). *)
(*     simpl in C; unfold C; set_iff; intuition. *)
(*     exists a; intuition. rewrite H; exact H0. *)
(*     destruct IHc as [y Hy]. intuition. *)
(*     exists y; intuition. *)
(*     apply IHl; auto. *)
(*     intros d Hd; apply Hsat; rewrite cfl_1 in Hd |- *; simpl. *)
(*     apply add_2; assumption. *)
(*   Qed. *)
(*   Remark model_expand_2 : *)
(*     forall M, model_expand M -> *)
(*       (forall l, l \In dom M -> *)
(*         (forall c, List.In c (L.expand l) -> *)
(*           exists y, List.In y c /\ M |= y)). *)
(*   Proof. *)
(*     intros; apply model_expand_1 with l; auto. *)
(*   Qed. *)
    
(*   Theorem dpll_dec (Pb : formula) : *)
(*     { incompatible (empty |- make Pb) } + *)
(*     { ~ incompatible (empty |- make Pb) }. *)
(*   Proof. *)
(*     intro Pb; case_eq (dpll Pb); unfold dpll. *)
(*     intros M Hsat; destruct (proof_search_sat *)
(*       (S (size (empty |- make Pb))) (empty |- make Pb) M *)
(*       (lt_n_Sn _) wf_empty (wexp_empty Pb) Hsat) *)
(*     as [Mwf [Mexp [Msub Msat]]]. *)

(*     (** Case where [proof_search] returns [Sat M] : *)
(*        We show that [completion M] is a model of our problem. *) *)
(*     assert (Mtrue : L.ltrue \In (dom M)) by *)
(*       (apply Msub; simpl; rewrite assumed_empty; apply singleton_2; auto). *)
(*     set (Model := @E.completion_model M Mwf Mtrue (model_expand_2 _ Mexp)). *)
(*     pose (Hsub := SemF.submodel_empty Model). *)
(*     right; intro Hincomp; apply (Hincomp Model). *)
(*     simpl; intro; rewrite assumed_empty; set_iff; intro Hl. *)
(*     rewrite <- (Sem.morphism _ _ _ Hl); apply Sem.wf_true. *)
(*     intros C HC; destruct (Msat C HC) as [l [Hl Hl']]. *)
(*     exists l; split; [ | exact Hl']. *)
(*     apply completion_extends; auto. *)

(*     (** Case where [proof_search] returns [Unsat] : trivial *)
(*        because derivability implies incompatibilty. *) *)
(*     intro Hsat; left; assert (H:=soundness _ (proof_search_unsat _ _ Hsat)). *)
(*     intros M HM; apply (H M); simpl; intros k. *)
(*     rewrite assumed_empty; set_iff; intro Hk. *)
(*     rewrite <- (Sem.morphism _ _ _ Hk); apply Sem.wf_true. *)
(*   Qed. *)

(*   (** A propositional version of completeness *) *)
(*   Lemma complete_model : *)
(*     forall (S : sequent) (M : E.t), *)
(*       wf_context (dom M) -> model_expand M -> *)
(*       dom (G S) [<=] dom M -> L.ltrue \In dom M -> *)
(*       sat_goal_e M (D S) -> *)
(*       {Mf : Sem.model | Sem.submodel (dom (G S)) Mf /\ Sem.sat_goal Mf (D S)}. *)
(*   Proof. *)
(*     intros S M Hwf Hwe Hsub Htrue Hsat. *)
(*     unfold model_expand in Hwe. *)
(*     pose (Model := @E.completion_model M Hwf Htrue (model_expand_2 M Hwe)). *)
(*     exists Model; split. *)
(*     intros l Hl; unfold Model; apply completion_extends. *)
(*     apply query_assumed; apply Hsub; auto. *)
(*     intros C HC; destruct (Hsat C HC) as [x [Hx1 Hx2]]; exists x; intuition. *)
(*     unfold Model; apply completion_extends; auto. *)
(*   Qed. *)
   
(*   Corollary completeness : *)
(*     forall S, *)
(*       wf_context (dom (G S)) -> wf_expand S -> L.ltrue \In dom (G S) -> *)
(*       incompatible S -> derivable S. *)
(*   Proof. *)
(*     intros S Hwf Hwe Htrue; case_eq (proof_search S (Datatypes.S (size S))). *)
(*     intros M HM Hinc. *)
(*     assert (wf_context (dom M) /\ model_expand M /\ *)
(*       dom (G S) [<=] dom M /\ sat_goal_e M (D S)). *)
(*     refine (proof_search_sat _ _ _ _ _ _ HM); auto. *)
(*     destruct H as [H1 [H2 [H3 H4]]]; *)
(*       destruct (complete_model _ M H1 H2 H3 (H3 _ Htrue) H4) as [Mf [Mf1 Mf2]]. *)
(*     contradiction (Hinc Mf Mf1 Mf2). *)
(*     intros Hunsat _; exact (proof_search_unsat _ _ Hunsat). *)
(*   Qed. *)
End SAT.