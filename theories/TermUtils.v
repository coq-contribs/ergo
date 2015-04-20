Require Import Containers.OrderedTypeEx.
Require Export Index List Term Rational.
Require Import Nfix.Nfix Containers.Generate.

Require Import Eqdep_dec.
Module DomainDT <: DecidableType.
  Definition U := arith_domain.
  Lemma eq_dec : forall x y:U, {x = y} + {x <> y}.
    decide equality.
  Qed.
End DomainDT.
Module DomainEqDep := DecidableEqDep(DomainDT).

Section Symbol_as_UOT.
  Section ArithDomain_as_UOT.
    Generate OrderedType arith_domain.
    Property arith_domain_eq_iff : forall s s', arith_domain_eq s s' <-> s = s'.
    Proof.
      induction s; destruct s'; split; intro H; subst;
        try (inversion_clear H); try constructor; auto.
    Qed.
    Global Instance arith_domain_UOT : UsualOrderedType arith_domain := {
      SOT_lt := arith_domain_lt;
      SOT_cmp := arith_domain_cmp
    }.
    Proof.
    + eauto.

    + constructor.
      - exact arith_domain_lt_trans.
      - intros; intro E; change (x = y) in E; rewrite <- arith_domain_eq_iff in E.
        exact (arith_domain_lt_irrefl _ _ H E).

    + intros; destruct (arith_domain_compare_spec x y); constructor; auto.
      exact (proj1 (arith_domain_eq_iff _ _) H).
    Defined.
  End ArithDomain_as_UOT.
  Definition arith_domain_OT : OrderedType arith_domain := SOT_as_OT.
  Existing Instance arith_domain_OT.

  Section Arithop_as_UOT.
    Generate OrderedType arithop.
    Property arithop_eq_iff : forall s s', arithop_eq s s' <-> s = s'.
    Proof.
      induction s; destruct s'; split; intro H; subst;
        try (inversion_clear H); try constructor; auto.
    Qed.

    Global Instance arithop_UOT : UsualOrderedType arithop := {
      SOT_lt := arithop_lt;
      SOT_cmp := arithop_cmp
    }.
    Proof.
    + eauto.
    + constructor.
      - exact arithop_lt_trans.
      - intros; intro E; change (x = y) in E; rewrite <- arithop_eq_iff in E.
        exact (arithop_lt_irrefl _ _ H E).
    + intros; destruct (arithop_compare_spec x y); constructor; auto.
      exact (proj1 (arithop_eq_iff _ _) H).
    Defined.
  End Arithop_as_UOT.
  Definition arithop_OT : OrderedType arithop := SOT_as_OT.
  Existing Instance arithop_OT.
  
  Definition compare_cst (d d' : arith_domain) 
    (c : dom_interp d) (c' : dom_interp d') : comparison :=
    match d as a, d' as b
      return dom_interp a -> dom_interp b -> comparison with
      | DomainNat, DomainNat => @compare nat _
      | DomainNat, _ => fun _ _ => Lt
      | _, DomainNat => fun _ _ => Gt
      | DomainN, DomainN => @compare N _
      | DomainN, _ => fun _ _ => Lt
      | _, DomainN => fun _ _ => Gt
      | DomainPos, DomainPos => @compare positive _
      | DomainPos, _ => fun _ _ => Lt
      | _, DomainPos => fun _ _ => Gt
      | DomainZ, DomainZ => @compare Z _
      | DomainZ, _ => fun _ _ => Lt
      | _, DomainZ => fun _ _ => Gt
      | DomainQ, DomainQ => @compare Qc _
    end c c'.
  
  Inductive symbol_lt : symbol -> symbol -> Prop :=
  | symbol_lt_Unint_1 :
    forall x y x' y', x <<< x' -> symbol_lt (Unint x y) (Unint x' y')
  | symbol_lt_Unint_2 :
    forall x y x' y', x === x' -> y <<< y' ->
      symbol_lt (Unint x y) (Unint x' y')
  | symbol_lt_Unint_Cst :
    forall x y d c, symbol_lt (Unint x y) (Cst d c)
  | symbol_lt_Unint_Op :
    forall x y d op, symbol_lt (Unint x y) (Op d op)
  | symbol_lt_Nat_1 :
    forall (c c' : nat), c <<< c'->
      symbol_lt (Cst DomainNat c) (Cst DomainNat c')
  | symbol_lt_Nat_N :
    forall c c', symbol_lt (Cst DomainNat c) (Cst DomainN c')
  | symbol_lt_Nat_Pos :
    forall c c', symbol_lt (Cst DomainNat c) (Cst DomainPos c')
  | symbol_lt_Nat_Z :
    forall c c', symbol_lt (Cst DomainNat c) (Cst DomainZ c')
  | symbol_lt_Nat_Q :
    forall c c', symbol_lt (Cst DomainNat c) (Cst DomainQ c')
  | symbol_lt_N_1 :
    forall (c c' : N), c <<< c'->
      symbol_lt (Cst DomainN c) (Cst DomainN c')
  | symbol_lt_N_Pos :
    forall c c', symbol_lt (Cst DomainN c) (Cst DomainPos c')
  | symbol_lt_N_Z :
    forall c c', symbol_lt (Cst DomainN c) (Cst DomainZ c')
  | symbol_lt_N_Q :
    forall c c', symbol_lt (Cst DomainN c) (Cst DomainQ c')
  | symbol_lt_Pos_1 :
    forall (c c' : positive), c <<< c'->
      symbol_lt (Cst DomainPos c) (Cst DomainPos c')
  | symbol_lt_Pos_Z :
    forall c c', symbol_lt (Cst DomainPos c) (Cst DomainZ c')
  | symbol_lt_Pos_Q :
    forall c c', symbol_lt (Cst DomainPos c) (Cst DomainQ c')
  | symbol_lt_Z_1 :
    forall (c c' : Z), c <<< c'->
      symbol_lt (Cst DomainZ c) (Cst DomainZ c')
  | symbol_lt_Z_Q :
    forall c c', 
      symbol_lt (Cst DomainZ c) (Cst DomainQ c')
  | symbol_lt_Q_1 :
    forall (c c' : Qc), c <<< c'->
      symbol_lt (Cst DomainQ c) (Cst DomainQ c')
  (*   | symbol_lt_Cst_1 :  *)
(*     forall d c d' c', d <<< d' -> symbol_lt (Cst d c) (Cst d' c') *)
(*   | symbol_lt_Cst_2_Nat :  *)
(*     forall (c c' : nat), c <<< c'->  *)
(*       symbol_lt (Cst DomainNat c) (Cst DomainNat c') *)
(*   | symbol_lt_Cst_2_N :  *)
(*     forall (c c' : N), c <<< c'->  *)
(*       symbol_lt (Cst DomainN c) (Cst DomainN c') *)
(*   | symbol_lt_Cst_2_Pos :  *)
(*     forall (c c' : positive), c <<< c'->  *)
(*       symbol_lt (Cst DomainPos c) (Cst DomainPos c') *)
(*   | symbol_lt_Cst_2_Z :  *)
(*     forall (c c' : Z), c <<< c'->  *)
(*       symbol_lt (Cst DomainZ c) (Cst DomainZ c') *)
  | symbol_lt_Cst_Op :
    forall d c d' op', symbol_lt (Cst d c) (Op d' op')
  | symbol_lt_Op_1 :
    forall d d' op op', d <<< d' -> symbol_lt (Op d op) (Op d' op')
  | symbol_lt_Op_2 :
    forall d d' op op', d === d' -> op <<< op' ->
      symbol_lt (Op d op) (Op d' op').

  Lemma cst_eq_dep :
    forall d c d' c', Cst d c = Cst d' c' -> 
      @EqdepFacts.eq_dep arith_domain dom_interp d c d' c'.
  Proof.
    intros.
    inversion H; simpl; reflexivity.
  Qed.
  Lemma inj_cst_2 : 
    forall d c c', Cst d c = Cst d c' -> c = c'.
  Proof.
    intros; apply DomainEqDep.eq_dep_eq; apply cst_eq_dep; assumption.
  Qed.

  Ltac dep_invert :=
    match goal with
      | H : Cst ?X ?y = Cst ?X ?z |- _ =>
        let IH := fresh "IH" in
          assert (IH := inj_cst_2 X y z H); subst; clear H
      | _ => idtac
    end.
  Property symbol_lt_trans : Transitive symbol_lt.
  Proof.
    intros [ty t|d c|e op]
      [ty' t'|d' c'|e' op']
      [ty'' t''|d'' c''|e'' op''];
      try (intro; inversion_clear 0;
        intro; inversion_clear 0;
          constructor; solve_by_trans_modulo);
      intros;
        try solve [constructor];
          try solve [inversion H | inversion H0 |
            destruct d; inversion H | destruct d'; inversion H0].
    destruct d; destruct d'; destruct d''; try solve
      [constructor | inversion H | inversion H0].
    inversion_clear H; inversion_clear H0; repeat dep_invert;
      constructor; solve_by_trans_modulo.
    inversion_clear H; inversion_clear H0; repeat dep_invert;
      constructor; solve_by_trans_modulo.
    inversion_clear H; inversion_clear H0; repeat dep_invert;
      constructor; solve_by_trans_modulo.
    inversion_clear H; inversion_clear H0; repeat dep_invert;
      constructor; solve_by_trans_modulo.
    inversion_clear H; inversion_clear H0; repeat dep_invert;
      constructor; solve_by_trans_modulo.
  Qed.
  Property symbol_lt_irrefl :
    forall s s', symbol_lt s s' -> s = s' -> False.
  Proof.
    intros; subst; destruct s'; try (inversion_clear H; solve [order]).
    destruct dom; inversion_clear H; repeat dep_invert; order.
  Qed.
  Definition symbol_StrictOrder :=
    Build_StrictOrder _ _ _ _ symbol_lt_trans symbol_lt_irrefl.

  Definition symbol_cmp (s s' : symbol) : comparison :=
    match s, s' with
      | Unint x y, Unint x' y' =>
        match x =?= x' with
          | Eq => y =?= y'
          | k => k
        end
      | _, Unint _ _ => Gt
      | Unint _ _, _ => Lt
      | Cst d c, Cst d' c' => compare_cst d d' c c'
      | Cst _ _, _ => Lt
      | _, Cst _ _ => Gt
      | Op d c, Op d' c' => 
        match d =?= d' with
          | Eq => c =?= c'
          | k => k
        end
    end.
  Property symbol_cmp_spec : 
    forall x y, compare_spec (@Logic.eq _) symbol_lt x y (symbol_cmp x y).
  Proof.
    destruct x; destruct y; simpl; try (constructor; constructor; auto).

    destruct (compare_dec ty_idx ty_idx0);
      try (constructor; constructor; auto).
    destruct (compare_dec t_idx t_idx0);
      try (constructor; ((constructor; solve [auto]) || congruence)).

    destruct dom; destruct dom0; simpl; try (constructor; constructor; auto);
      set (Hc := compare_dec z z0); inversion Hc;
        constructor; ((constructor; solve [auto]) || congruence).

    destruct (compare_dec dom dom0);
      try (constructor; constructor; auto).
    destruct (compare_dec op op0);
      try (constructor; ((constructor; solve [auto]) || congruence)).
  Qed.

  Global Instance symbol_UOT : UsualOrderedType symbol := {
    SOT_lt := symbol_lt;
    SOT_cmp := symbol_cmp;
    SOT_StrictOrder := symbol_StrictOrder;
    SOT_compare_spec := symbol_cmp_spec
  }.
End Symbol_as_UOT.

Definition symbol_OT : OrderedType symbol := SOT_as_OT.
Existing Instance symbol_OT.

Nested Fixpoint cmp_term (t u : term) : comparison :=
  match t, u with
    | app f l, app g l' =>
      match f =?= g with
        | Eq => cmp_terms l l'
        | Lt => Lt
        | Gt => Gt
      end
  end
  with cmp_terms (ts us : terms) : comparison :=
    match ts, us with
      | nil, nil => Eq
      | nil, cons _ _ => Lt
      | cons _ _, nil => Gt
      | cons t tq, cons u uq =>
        match cmp_term t u with
          | Eq => cmp_terms tq uq
          | Lt => Lt | Gt => Gt
        end
    end.

Section TermMutualInduction.
  Variable P : term -> Prop.
  Variable Pl : terms -> Prop.

  Variable Happ : forall (f : symbol) (lt : terms), Pl lt -> P (app f lt).
  Variable Hnil : Pl tnil.
  Variable Hcons : forall t, P t -> forall lt, Pl lt -> Pl (tcons t lt).
  
  Theorem term_mutual_ind : (forall t : term, P t) /\ (forall l : terms, Pl l).
  Proof.
    assert (I := term_terms_rect P Pl Happ Hnil Hcons); 
      split; [exact I| induction l; auto].
  Qed.
End TermMutualInduction.
Definition term_terms_rect_default (P : term -> Prop)
  (H : forall (f : symbol) (lt : terms),
    (forall t : term, In t lt -> P t) -> P (app f lt)) :
  forall t, P t.
Proof.
  refine (term_terms_rect P (fun lt => forall t, List.In t lt -> P t) H _ _).
  intros; contradiction H0.
  intros; inversion_clear H2; subst; auto.
Qed.

Definition term_lt (t u : term) := cmp_term t u = Lt.
Definition terms_lt (lt lu : terms) := cmp_terms lt lu = Lt.

Theorem cmp_term_terms_eq :
  (forall t, (fun t => forall u, cmp_term t u = Eq <-> t = u) t) /\
  (forall lt, (fun lt => forall lu, cmp_terms lt lu = Eq <-> lt = lu) lt).
Proof.
  apply term_mutual_ind.
  (* - Happ *)
  intros f lt IH [g lu]; simpl; destruct (compare_dec f g).
  split; intro abs; try discriminate abs; inversion abs; order.
  rewrite IH, H; split; congruence.
  split; intro abs; try discriminate abs; inversion abs; order.
  (* - Hnil *)
  intros [|? ?]; simpl; split; intro; auto; discriminate.
  (* - Hcons *)
  intros t IH lt IHl [|u lu]; simpl.
  split; intro; discriminate.
  case_eq (cmp_term t u); intro Ht; rewrite ?IH in Ht; subst.
  rewrite IHl; split; congruence.
  split; intro abs; try discriminate; 
    inversion abs; rewrite <-IH in *; congruence.
  split; intro abs; try discriminate; 
    inversion abs; rewrite <-IH in *; congruence.
Qed.
Definition cmp_term_eq := Eval simpl in proj1 (cmp_term_terms_eq).
Definition cmp_terms_eq := Eval simpl in proj2 (cmp_term_terms_eq).

Corollary term_lt_not_eq : forall t u, term_lt t u -> t <> u.
Proof. 
  intros t u; rewrite <- cmp_term_eq; unfold term_lt; congruence.
Qed.
Corollary terms_lt_not_eq : forall lt lu, terms_lt lt lu -> lt <> lu.
Proof. 
  intros lt lu; rewrite <- cmp_terms_eq; unfold terms_lt; congruence.
Qed.

Theorem term_terms_lt_trans :
  (forall t, (fun t => forall u v, 
    term_lt t u -> term_lt u v -> term_lt t v) t) /\
  (forall lt, (fun lt => forall lu lv, 
    terms_lt lt lu -> terms_lt lu lv -> terms_lt lt lv) lt).
Proof.
  apply term_mutual_ind.
  (* - Happ *)
  intros f lt IH [g lu] [h lv]; unfold term_lt; simpl.
  destruct (compare_dec f g); destruct (compare_dec g h); 
    intros E1 E2; try discriminate.
  rewrite elim_compare_lt; auto; transitivity g; assumption.
  rewrite elim_compare_lt; auto; apply lt_eq with g; assumption.
  rewrite elim_compare_lt; auto; apply eq_lt with g; auto using symmetry.
  rewrite elim_compare_eq. 
    unfold terms_lt in IH; eauto. transitivity g; assumption.
  (* - Hnil *)
  intros [|u lu] [|v lv]; unfold terms_lt; simpl; intros; auto; discriminate.
  (* - Hcons *)
  intros t IH lt IHl [|u lu] [|v lv]; unfold terms_lt; 
    simpl; try (intros; discriminate).
  case_eq (cmp_term t u); intro Ht.
  rewrite cmp_term_eq in Ht; subst.
  destruct (cmp_term u v); intros; auto; unfold terms_lt in IHl; eauto.
  case_eq (cmp_term u v); intro Hu.
  rewrite cmp_term_eq in Hu; subst; auto.
  rewrite Ht; auto.
  rewrite (IH _ _ Ht Hu); auto.
  intros; discriminate.
  intros; discriminate.
Qed.
Definition term_lt_trans := Eval simpl in proj1 (term_terms_lt_trans).
Definition terms_lt_trans := Eval simpl in proj2 (term_terms_lt_trans).

Theorem cmp_term_terms_sym : 
  (forall t, (fun t => forall u, 
    cmp_term t u = CompOpp (cmp_term u t)) t) /\
  (forall lt, (fun lt => forall lu, 
    cmp_terms lt lu = CompOpp (cmp_terms lu lt)) lt).
Proof.
  apply term_mutual_ind.
  (* - Happ *)
  intros f lt IH [g lu]; simpl.
  destruct (compare_dec f g).
  rewrite (elim_compare_gt H); split; auto.
  rewrite (elim_compare_eq (symmetry H)); apply IH.
  rewrite (elim_compare_lt H); split; auto.
  (* - Hnil *)
  intros [|u lu]; simpl; intros; split; congruence.
  (* - Hcons *)
  intros t IH lt IHl [|u lu]; simpl; auto.
  rewrite IH, IHl; destruct (cmp_term u t); auto.
Qed.
Definition cmp_term_sym := Eval simpl in proj1 (cmp_term_terms_sym).
Definition cmp_terms_sym := Eval simpl in proj2 (cmp_term_terms_sym).

Corollary cmp_term_spec :
  forall t u, compare_spec (@Logic.eq _) term_lt t u (cmp_term t u).
Proof.
  intros; case_eq (cmp_term t u); intro Ht; constructor.
  rewrite cmp_term_eq in Ht; exact Ht.
  exact Ht.
  hnf; rewrite cmp_term_sym; rewrite Ht; reflexivity.
Qed.

Corollary cmp_terms_spec :
  forall lt lu, compare_spec (@Logic.eq _) terms_lt lt lu (cmp_terms lt lu).
Proof.
  intros; case_eq (cmp_terms lt lu); intro Hlt; constructor.
  rewrite cmp_terms_eq in Hlt; exact Hlt.
  exact Hlt.
  hnf; rewrite cmp_terms_sym; rewrite Hlt; reflexivity.
Qed.

Instance term_UOT : UsualOrderedType term := {
  SOT_lt := term_lt;
  SOT_StrictOrder := Build_StrictOrder _ _ _ _ term_lt_trans term_lt_not_eq;
  SOT_cmp := cmp_term;
  SOT_compare_spec := cmp_term_spec
}.
Definition term_OT : OrderedType term := SOT_as_OT.
Existing Instance term_OT.

Instance terms_UOT : UsualOrderedType terms := {
  SOT_lt := terms_lt;
  SOT_StrictOrder := Build_StrictOrder _ _ _ _ terms_lt_trans terms_lt_not_eq;
  SOT_cmp := cmp_terms;
  SOT_compare_spec := cmp_terms_spec
}.
Definition terms_OT : OrderedType terms := SOT_as_OT.
Existing Instance terms_OT.
