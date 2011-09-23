Require Import Maps Sets SetProperties.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Section AnyOrderedType.
  Context `{term_OT : OrderedType term}.

  SubClass t := Map[term, set term].
  
  Definition empty : t := [].
  
  Definition neqs (d : t) (a : term) : set term :=
    match d[a] with
      | Some s => s
      | None => {}
    end.
  
  Definition separate (d : t) (a b : term) : t :=
    insert a {b} (add b) (insert b {a} (add a) d).
  
  Definition are_diff (d : t) (a b : term) : bool :=
    a \in neqs d b.
  Global Coercion are_diff : t >-> Funclass.

  (** The properties that the Diff data structure must verify
     are rather easy ; it still helps in CC if the structure
     verifies a symmetry invariant. *)
  Section WithSpecs.
    
    Class Wf (d : t) := {
      is_wf : forall a b, d a b = d b a
    }.

    (* About [neqs] *)
    Property neqs_iff : 
      forall d a b, a \In neqs d b <-> d a b = true.
    Proof.
      intros d a b; apply mem_iff.
    Qed.
    Property neqs_not_iff : 
      forall d a b, (~ a \In neqs d b) <-> d a b = false.
    Proof.
      intros d a b; apply not_mem_iff.
    Qed.

    Instance neqs_m : Proper
      (@Logic.eq _ ==> _eq ==> @Logic.eq _) neqs.
    Proof.
      repeat intro; unfold neqs; subst.
      case_eq (y[x0]); intros.
      rewrite H0 in H; rewrite H; reflexivity.
      rewrite H0 in H; rewrite H; reflexivity.
    Qed.
    Instance are_diff_m : Proper
      (@Logic.eq _ ==> _eq ==> _eq ==> @Logic.eq bool) are_diff.
    Proof.
      repeat intro; subst.
      case_eq (y x0 x1); intros; symmetry.
      rewrite <- neqs_iff in *.
      rewrite <- H0, <- H1; exact H.
      rewrite <- neqs_not_iff in *.
      rewrite <- H0, <- H1; exact H.
    Qed.

    Remark neqs_sym : forall `{Wf d} a b, a \In neqs d b <-> b \In neqs d a.
    Proof.
      intros; rewrite 2neqs_iff; rewrite is_wf; reflexivity.
    Qed.

    (* About [empty] *)
    Property are_diff_empty : forall a b, empty a b = false.
    Proof.
      intros; reflexivity.
    Qed.
    Corollary neqs_empty : forall a, neqs empty a [=] {}.
    Proof.
      intros; intro b; rewrite neqs_iff, are_diff_empty.
      split; intro H; [discriminate H | contradiction (empty_1 H)].
    Qed.
    
    Instance Wf_empty : Wf empty.
    Proof. constructor.
      intros; rewrite 2are_diff_empty; reflexivity.
    Qed.
      
    (* About [separate] *)
    Property insert_eq_o : 
      forall (m : t) k d f k', k === k' -> (insert k d f m)[k'] =
        match m[k'] with Some r => Some (f r) | None => Some d end.
    Proof.
      intros.
      destruct m[k'] as [sk'|]_eqn:Hk'.
      apply find_1; apply insert_1; auto using find_2.
      apply find_1; apply insert_2; auto using find_2.
      rewrite MapFacts.not_find_in_iff; assumption.
    Qed.
    Property insert_neq_o : 
      forall (m : t) k d f k', k =/= k' -> (insert k d f m)[k'] = m[k'].
    Proof.
      intros.
      destruct m[k'] as [sk'|]_eqn:Hk'.
      apply find_1; apply insert_3; auto using find_2.
      destruct (insert k d f m)[k'] as [sik'|]_eqn; auto.
      assert (Hz := insert_4 H (find_2 Heqo)).
      rewrite (find_1 Hz) in Hk'; discriminate.
    Qed.

    Property neqs_separate_1 : forall d a b,
      neqs (separate d a b) a [=] {b; neqs d a}.
    Proof.
      intros; unfold neqs, separate.
      destruct (eq_dec a b).
      rewrite !insert_eq_o by auto.
      destruct d[a]; rewrite H.
      apply add_equal; apply add_1; reflexivity.
      rewrite singleton_equal_add; apply add_equal; apply add_1; reflexivity.
      rewrite insert_eq_o by auto.
      rewrite insert_neq_o by (symmetry; auto).
      destruct d[a]; try reflexivity.
      apply singleton_equal_add.
    Qed.
    Property neqs_separate_2 : forall d a b,
      neqs (separate d a b) b [=] {a; neqs d b}.
    Proof.
      intros; unfold neqs, separate.
      destruct (eq_dec a b).
      rewrite !insert_eq_o by auto.
      destruct d[b]; rewrite H.
      apply add_equal; apply add_1; reflexivity.
      rewrite singleton_equal_add; apply add_equal; apply add_1; reflexivity.
      rewrite insert_neq_o by (auto).
      rewrite insert_eq_o by auto.
      destruct d[b]; try reflexivity.
      apply singleton_equal_add.
    Qed.
    Property neqs_separate_3 : forall d a b c,
      a =/= c -> b =/= c -> neqs (separate d a b) c [=] neqs d c.
    Proof.
      intros; unfold neqs, separate.
      rewrite 2insert_neq_o by auto.
      reflexivity.
    Qed.

    Corollary are_diff_separate_1 : forall d a b,
      (separate d a b) a b = true.
    Proof.
      intros; unfold are_diff.
      rewrite neqs_separate_2; apply mem_1; apply add_1; auto.
    Qed.
    Corollary are_diff_separate_2 : forall d a b,
      (separate d a b) b a = true.
    Proof.
      intros; unfold are_diff.
      rewrite neqs_separate_1; apply mem_1; apply add_1; auto.
    Qed.
    Property are_diff_separate_3 : forall d a b a' b',
      (a =/= a' /\ b =/= a' \/ a =/= b' /\ b =/= b') -> 
      (separate d a b) a' b' = d a' b'.
    Proof.
      intros; unfold are_diff.
      destruct (eq_dec b b').
      rewrite <- H0, neqs_separate_2.
      destruct H as [[E1 E2]|[E1 E2]]; try contradiction.
      rewrite add_b; destruct (eq_dec a a'); try contradiction; reflexivity.
      destruct (eq_dec a b').
      rewrite <- H1, neqs_separate_1.
      destruct H as [[E1 E2]|[E1 E2]]; try contradiction.
      rewrite add_b; destruct (eq_dec b a'); try contradiction; reflexivity.
      rewrite (neqs_separate_3 d H1 H0); reflexivity.
    Qed.
  
    Corollary separate_conservative : 
      forall (d : t) a b x y, d x y = true -> (separate d a b) x y = true.
    Proof.
      intros; rewrite <- neqs_iff in *.
      destruct (eq_dec a y).
      rewrite <- H0, neqs_separate_1, H0; apply add_2; assumption.
      destruct (eq_dec b y).
      rewrite <- H1, neqs_separate_2, H1; apply add_2; assumption.
      rewrite neqs_separate_3; assumption.
    Qed.

    Instance Wf_separate `{Wf d} (a b : term) : Wf (separate d a b).
    Proof.
      intros; constructor; intros.
      destruct (eq_dec a a0); destruct (eq_dec a b0);
        try (rewrite <- H0, <- H1; reflexivity);
          destruct (eq_dec b a0); destruct (eq_dec b b0);
            try (rewrite <- H2, <- H3; reflexivity).
      rewrite (@are_diff_separate_3 d a b a0 b0) by (right; split; assumption).
      rewrite (@are_diff_separate_3 d a b b0 a0) by (left; split; assumption).
      apply is_wf.
      rewrite <- H0, <- H3, are_diff_separate_1, are_diff_separate_2; trivial.
      rewrite (@are_diff_separate_3 d a b a0 b0) by (right; split; assumption).
      rewrite (@are_diff_separate_3 d a b b0 a0) by (left; split; assumption).
      apply is_wf.
      rewrite <- H1, <- H2, are_diff_separate_1, are_diff_separate_2; trivial.
      rewrite (@are_diff_separate_3 d a b a0 b0) by (left; split; assumption).
      rewrite (@are_diff_separate_3 d a b b0 a0) by (right; split; assumption).
      apply is_wf.
      rewrite (@are_diff_separate_3 d a b a0 b0) by (left; split; assumption).
      rewrite (@are_diff_separate_3 d a b b0 a0) by (right; split; assumption).
      apply is_wf.
      rewrite (@are_diff_separate_3 d a b a0 b0) by (right; split; assumption).
      rewrite (@are_diff_separate_3 d a b b0 a0) by (left; split; assumption).
      apply is_wf.
      rewrite (@are_diff_separate_3 d a b a0 b0) by (left; split; assumption).
      rewrite (@are_diff_separate_3 d a b b0 a0) by (right; split; assumption).
      apply is_wf.
      rewrite (@are_diff_separate_3 d a b a0 b0) by (left; split; assumption).
      rewrite (@are_diff_separate_3 d a b b0 a0) by (right; split; assumption).
      apply is_wf.
    Qed.
  End WithSpecs.
End AnyOrderedType.

Global Opaque t empty neqs separate are_diff.