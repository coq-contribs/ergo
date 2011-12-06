Require Import Sets Maps.
Require Import Theory.
Require Import Term.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Section WithTheory.
  Context `{Th : Theory}.

  Structure t_ := mk_t { 
    this :> Map[term, R];
    canon : term -> R
  }.
  Definition t := t_.

  Definition empty : t := mk_t [] make.
  
  Definition find (m : t) (t : term) : R :=
    match m[t] with
      | Some r => r
      | None => canon m t
    end.
  Global Coercion find : t >-> Funclass.

  Definition mem (m : t) (a : term) : bool := mem a m.
  Definition add (m : t) (a : term) : t :=
    match m[a] with
      | Some _ => m
      | None => mk_t (m[a <- canon m a]) (canon m) 
    end.

  Definition merge (m : t) (p P : R) : t :=
    mk_t (map (subst p P) m) (fun t => subst p P (canon m t)).

  Definition merge_touched (m : Map[term,R]) (p P : R) :
    Map[term,R] * terms :=
    fold (key:=term) (fun a rep mt =>
      let '(m, touched) := mt in
        let rep' := subst p P rep in
          if rep == rep' then mt
            else (m[a <- rep'], a::touched))
    m (m, nil).
  
  Definition merge' (m : t) (p P : R) : t * list term :=
    let '(m', touched) := merge_touched m p P in
      (mk_t m' (fun t => subst p P (canon m t)), touched).
  
  Definition congruent (m : t) (a b : term) : bool :=
    m a == m b.

  (* The next 3 functions used to be useful but not anymore *)
  Definition range (m : t) : set term :=
    fold (fun k _ acc => {k; acc}) m {}.
  Definition reprs (m : t) : set R :=
    fold (fun _ r acc => {r; acc}) m {}.
  Definition num_classes (m : t) : nat := SetInterface.cardinal (reprs m).
End WithTheory.

Section WithTheorySpecs.
  Context `{Th: Theory}.

  (** The UF map [{this; canon}] is well-formed if it such that
     [this] maps terms [t] to [canon t]. In other terms, while 
     [canon] accumulates all the merges in the structure, the
     map [this] memoizes the result of [canon] on the terms
     that have been added. *)
  Class Wf (m : t) := {
    is_wf : forall t, mem m t = true -> m t === canon m t
  }.

  (* About empty *)
  Property empty_mem : forall t, mem empty t = false.
  Proof. 
    intros; unfold mem; simpl; apply MapFacts.empty_a. 
  Qed.

  Instance Wf_empty : Wf empty.
  Proof.
    constructor; intros.
    rewrite empty_mem in H; discriminate.
  Qed.

  Property empty_find : forall t, empty t = make t.
  Proof. 
    intro; reflexivity. 
  Qed.
    
  (* About add *)
  Property add_mem_1 : forall m a, mem (add m a) a = true.
  Proof.
    intros; unfold mem, add; simpl.
    rewrite MapFacts.mem_find_b.
    case_eq (m[a]); intros; simpl.
    rewrite H; reflexivity.
    rewrite MapFacts.add_eq_o; auto.
  Qed.
  Property add_mem_2 : forall m a t, mem m t = true -> mem (add m a) t = true.
  Proof.
    intros; unfold mem, add; simpl.
    rewrite MapFacts.mem_find_b.
    case_eq (m[a]); intros; simpl.
    rewrite <- MapFacts.mem_find_b; exact H.
    rewrite MapFacts.add_neq_o.
    rewrite <- MapFacts.mem_find_b; exact H.
    intro R; rewrite R in H0.
    unfold mem in H; rewrite MapFacts.mem_find_b in H.
    rewrite H0 in H; discriminate.
  Qed.
  Property add_mem_3 : forall m a t, mem (add m a) t = true ->
    a <> t -> mem m t = true.
  Proof.
    intros; unfold mem, add in *; simpl in *.
    rewrite MapFacts.mem_find_b in *.
    case_eq (m[t0]); intros; simpl; auto.
    case_eq (m[a]); intros; simpl; rewrite H2 in H.
    rewrite MapFacts.mem_find_b in H; rewrite H1 in H; discriminate.
    rewrite MapFacts.mem_find_b in H; unfold find in H; simpl in H.
    rewrite MapFacts.add_neq_o, H1 in H; auto; discriminate.
  Qed.
  Corollary add_mem_iff : forall m a t,
    mem (add m a) t = true <-> a === t \/ mem m t = true.
  Proof.
    intros; destruct (eq_dec a t0); split; intro.
    left; assumption.
    rewrite H; apply add_mem_1.
    right; apply add_mem_3 with a; auto.
    destruct H0; try contradiction; apply add_mem_2; auto.
  Qed.

  Instance Wf_add `{Wf m} (a : term) : Wf (add m a).
  Proof.
    constructor; intros.
    destruct (eq_dec a t0).
    rewrite H1 in *; clear H1.
    unfold add, find in *; simpl in *.
    case_eq (m[t0]); intros; rewrite H1 in *.
    assert (r = m t0).
    unfold find; rewrite H1; auto.
    rewrite H2; apply is_wf; auto.
    unfold add, find in *; simpl in *.
    rewrite MapFacts.add_eq_o; auto.
    assert (Ht := add_mem_3 H0 H1); clear H0.
    unfold add, find; simpl.
    case_eq (m[a]); intros; auto.
    unfold mem in Ht; rewrite MapFacts.mem_find_b in Ht.
    case_eq (m[t0]); intros.
    assert (r0 = m t0).
    unfold find; rewrite H2; auto.
    rewrite H3; apply is_wf; auto.
    rewrite <- MapFacts.mem_find_b in Ht; exact Ht.
    rewrite H2 in Ht; discriminate.
    unfold find; simpl.
    rewrite MapFacts.add_neq_o; auto.
    case_eq (m[t0]); intros; auto.
    assert (r = m t0).
    unfold find; rewrite H2; auto.
    rewrite H3; apply is_wf; auto.
  Qed.

  Property add_find_1 : forall m `{Wf m} a, find (add m a) a === canon m a.
  Proof.
    intros; assert (Ha := @is_wf m H a); 
      unfold mem, add, find, canon in *; simpl in *.
    rewrite MapFacts.mem_find_b in Ha.
    destruct m[a] as [ra|]_eqn:Hma.
    rewrite Hma; exact (Ha (refl_equal _)).
    destruct m as [m can]; simpl in *.
    rewrite MapFacts.add_eq_o; reflexivity.
  Qed.
  Property add_find_2 : 
    forall m a a', a =/= a' -> find (add m a) a' = find m a'.
  Proof.
    intros.
    unfold add, find in *; destruct m as [m can]; simpl in *.
    destruct m[a] as [ra|]_eqn:Hma; simpl.
    reflexivity.
    rewrite MapFacts.add_neq_o; trivial.
  Qed.
  Property add_find : forall m `{Wf m} a a', find (add m a) a' === find m a'.
  Proof.
    intros.
    unfold add, find in *; destruct m as [m can]; simpl in *.
    destruct m[a] as [ra|]_eqn:Hma; simpl.
    reflexivity.
    destruct (eq_dec a a').
    rewrite MapFacts.add_eq_o; trivial.
    rewrite H0 in Hma; rewrite Hma; rewrite H0; reflexivity.
    rewrite MapFacts.add_neq_o; trivial.
  Qed.

  Remark add_conservative :
    forall (m : t) a x y, m x === m y -> (add m a) x === (add m a) y.
  Proof.
    intros; unfold add, find, mem in *; simpl in *.
    destruct m[a] as [ra|]_eqn:Ha; simpl in *.
    assumption.
    destruct (eq_dec a x).
    rewrite MapFacts.add_eq_o by auto.
    destruct (eq_dec a y).
    rewrite MapFacts.add_eq_o; auto.
    rewrite MapFacts.add_neq_o by auto.
    rewrite H0 in *; rewrite Ha in H; assumption.
    rewrite MapFacts.add_neq_o by auto; rewrite H; clear H.
    destruct (eq_dec a y).
    rewrite MapFacts.add_eq_o; auto.
    rewrite H in *; rewrite Ha; reflexivity.
    rewrite MapFacts.add_neq_o; auto.
  Qed.

  (* About merge *)
  Property merge_mem :
    forall m p P t, mem (merge m p P) t = mem m t.
  Proof.
    intros; unfold mem, merge; simpl.
    apply MapFacts.map_b.
  Qed.

  Instance Wf_merge `{ThSpecs : @TheorySpecs Th, Wf m} 
    (p P : R) : Wf (merge m p P).
  Proof.
    constructor; intros.
    unfold merge, mem, find in *; simpl in *.
    rewrite MapFacts.map_o.
    rewrite MapFacts.map_b in H0.
    assert (Ht := is_wf H0).
    rewrite MapFacts.mem_find_b in H0.
    unfold find in Ht; simpl in Ht.
    destruct (m[t0]); simpl.
    rewrite Ht; reflexivity.
    reflexivity.
  Qed.

  Property merge_find :
    forall m p P t, (merge m p P) t = subst p P (m t).
  Proof.
    intros; unfold find, merge; simpl.
    rewrite !MapFacts.map_o.
    destruct m[t0]; simpl; reflexivity.
  Qed.

  (* About merge' *)
  Definition merge_touched_spec (m : Map[term, R]) (p P : R)
    (mvu : Map[term, R]) (mt : Map[term, R] * list term) :=
    forall t, MapInterface.mem t (fst mt) = MapInterface.mem t m.
  Property merge_touched_mem :
    forall m p P t, MapInterface.mem t (fst (merge_touched m p P))
      = MapInterface.mem t m.
  Proof.
    intros m p P; apply (@MapFacts.fold_rec_bis _ _ _ _ _ _
      (merge_touched_spec m p P)).
    (* - morphism *)
    intros m1 m2 [mr tr] Heq; unfold merge_touched_spec; simpl; intros.
    exact (H t0).
    (* - empty *)
    intro; reflexivity.
    (* - add *)
    intros a r [mr tr] m' Hm Hk; unfold merge_touched_spec; simpl; intros.
    destruct (eq_dec r (subst p P r)); simpl; auto.
    rewrite MapFacts.add_b.
    destruct (eq_dec a t0); simpl; auto.
    symmetry; rewrite <- MapFacts.mem_in_iff; exists r; rewrite <- H1; auto.
  Qed.
  Corollary merge'_mem :
    forall m p P t, mem (fst (merge' m p P)) t = mem m t.
  Proof.
    intros m p P t0; unfold mem, merge'; destruct m as [m can]; simpl.
    assert (H := merge_touched_mem m p P t0); revert H.
    case_eq (merge_touched m p P); intro; simpl; auto.
  Qed.
    
  Definition merge_touched_spec_2 (m : Map[term, R]) (p P : R)
    (mvu : Map[term, R]) (mt : Map[term, R] * list term) :=
    forall t, MapInterface.find t (fst mt) ===
      match MapInterface.find t mvu with 
        | Some r => Some (subst p P r)
        | None => MapInterface.find t m
      end.
  Property merge_touched_find :
    forall m p P, 
    merge_touched_spec_2 m p P m (merge_touched m p P).
(* TODO : Why does this expanded version of the statement take forever to typecheck ?!
      MapInterface.find t (fst (merge_touched m p P)) ===
      match MapInterface.find t m with
        | Some r => Some (subst p P r)
        | None => MapInterface.find t m
      end.
*)
  Proof.
    unfold merge_touched_spec_2.
    intros m p P; apply (@MapFacts.fold_rec_bis _ _ _ _ _ _
      (merge_touched_spec_2 m p P)).
    (* - morphism *)
    intros m1 m2 [mr tr] Heq; unfold merge_touched_spec_2; simpl; intros.
    rewrite <- Heq; apply H.
    (* - empty *)
    intros t0; rewrite MapFacts.empty_o; reflexivity.
    (* - add *)
    intros a r [mr tr] m' Hm Hk; unfold merge_touched_spec_2; simpl; intros.
    assert (H0 := H t0); clear H.
    destruct (eq_dec r (subst p P r)); simpl.
    destruct (eq_dec a t0); simpl; auto.
    rewrite H1 in *; clear H1.
    rewrite MapFacts.add_eq_o; auto.
    rewrite MapFacts.not_find_in_iff in Hk; rewrite Hk in H0.
    rewrite MapFacts.find_mapsto_iff in Hm.
    rewrite H0, Hm; constructor; exact H.
    rewrite MapFacts.add_neq_o; auto.
    destruct (eq_dec a t0); simpl.
    rewrite H1 in *; clear H1.
    rewrite !MapFacts.add_eq_o in *; auto.
    rewrite !MapFacts.add_neq_o; auto.
  Qed.
  Corollary merge'_find :
    forall m p P t, find (fst (merge' m p P)) t === subst p P (find m t).
  Proof.
    intros; unfold find, merge'; simpl.
    assert (H := merge_touched_find m p P t0).
    destruct (merge_touched m p P) as [mr tr]; simpl in *.
    destruct (m[t0]).
    inversion H; subst; auto.
    inversion H; reflexivity.
  Qed.
  
  Instance Wf_merge' `{ThSpecs : @TheorySpecs Th, Wf m} 
    (p P : R) : Wf (fst (merge' m p P)).
  Proof.
    constructor; intros.
    rewrite merge'_find.
    rewrite merge'_mem in H0.
    unfold merge'; simpl in *.
    destruct (merge_touched m p P) as [ ]_eqn; simpl in *.
    apply subst_m; auto; apply is_wf; auto.
  Qed.

  (* About congruent *)
  Inductive congruent_spec (m : t) (a b : term) : bool -> Prop :=
  | congruent_true : m a === m b -> congruent_spec m a b true
  | congruent_false : m a =/= m b -> congruent_spec m a b false.
  Theorem congruent_dec : forall m a b, 
    congruent_spec m a b (congruent m a b).
  Proof.
    intros; unfold congruent; destruct (eq_dec (m a) (m b));
      constructor (auto).
  Qed.

  (* About range *)  
  Property range_mem : forall m t, mem m t = (t \in range m).
  Proof.
    intros; unfold mem, range in *; destruct m as [m can]; simpl.
    apply (@MapFacts.fold_rec_bis _ _ _ _ _ _
      (fun m' a => MapInterface.mem t0 m' = (t0 \in a))); 
    intros; simpl in *.
    rewrite MapFacts.mem_find_b in H0 |- *; rewrite <- H; exact H0.
    reflexivity.
    destruct (eq_dec k t0).
    rewrite MapFacts.add_eq_b; auto.
    symmetry; apply SetInterface.mem_1; apply SetInterface.add_1; auto.
    rewrite MapFacts.add_neq_b; auto.
    rewrite SetFacts.add_neq_b; auto.
  Qed.

  Property range_empty : range empty [=] {}.
  Proof.
    reflexivity.
  Qed.
  Property range_add : forall a m, range (add m a) [=] {a; range m}.
  Proof.
    intros a m u; rewrite SetFacts.add_iff, !SetFacts.mem_iff.
    rewrite <- !range_mem.
    apply add_mem_iff.
  Qed.
  Property range_merge : forall m u v, range (merge m u v) [=] range m.
  Proof.
    intros m u v a.
    rewrite !SetFacts.mem_iff, <- !range_mem, merge_mem.
    reflexivity.
  Qed.
  Property range_merge' : forall m u v, range (fst (merge' m u v)) [=] range m.
  Proof.
    intros m u v a.
    rewrite !SetFacts.mem_iff, <- !range_mem, merge'_mem.
    reflexivity.
  Qed.

  (* About reprs *)
  Property reprs_mem : 
    forall (m : t) r, 
      (exists t, m[t] === Some r) <-> SetInterface.In r (reprs m).
  Proof.
    intros; unfold find, reprs in *; destruct m as [m can]; simpl.
    apply (@MapFacts.fold_rec_bis _ _ _ _ _ _
      (fun m' a => (exists t, m'[t] === Some r) <-> r \In a));
    intros; simpl in *.
    (* - morphism *)
    rewrite <- H0; split; intros [u Hu]; exists u.
    rewrite H; assumption. rewrite <- H; assumption.
    (* - empty *)
    split; intro H.
    destruct H; rewrite MapFacts.empty_o in H; inversion H.
    contradiction (SetInterface.empty_1 H).
    (* - add *)
    rewrite SetFacts.add_iff, <- H1; split; intro Z; clear H1.
    destruct Z as [u Hu].
    destruct (eq_dec k u); [left | right].
    rewrite MapFacts.add_eq_o in Hu; auto.
    inversion Hu; assumption.
    rewrite MapFacts.add_neq_o in Hu; auto; exists u; auto.
    destruct Z as [Heq | [u  Hu]].
    exists k; rewrite MapFacts.add_eq_o; auto; constructor; auto.
    destruct (eq_dec k u); [exists k | exists u].
    rewrite H1 in *; rewrite MapFacts.not_find_in_iff in H0.
    rewrite H0 in Hu; inversion Hu.
    rewrite MapFacts.add_neq_o; auto.
  Qed.

  Property reprs_empty : reprs empty [=] {}.
  Proof.
    reflexivity.
  Qed.
  Property reprs_add_1 : forall a m, reprs (add m a) [<=] {canon m a; reprs m}.
  Proof.
    intros a m r; rewrite SetFacts.add_iff, <- !reprs_mem; intro.
    destruct H as [u Hu].
    unfold add in Hu; simpl in Hu; destruct m[a].
    right; exists u; auto.
    destruct (eq_dec a u); simpl in Hu.
    rewrite MapFacts.add_eq_o in Hu; auto; inversion_clear Hu; left; auto.
    rewrite MapFacts.add_neq_o in Hu; auto; right; exists u; auto.
  Qed.
  Property reprs_add_2 : forall a m, reprs m [<=] reprs (add m a).
  Proof.
    intros a m r; rewrite <- !reprs_mem; intro.
    destruct H as [u Hu].
    destruct (eq_dec a u); simpl.
    exists u; rewrite H in *.
    unfold add; simpl; destruct m[u] as [ ]_eqn.
    inversion Hu; rewrite Heqo; auto.
    inversion Hu.
    exists u; unfold add; simpl; destruct m[a]; auto.
    simpl; rewrite MapFacts.add_neq_o ; auto.
  Qed.
  Property reprs_merge `{ThSpecs : @TheorySpecs Th} : 
    forall m p P r, r \In reprs (merge m p P) <-> 
    (exists r', r' \In reprs m /\ subst p P r' === r).
  Proof.
    intros m p P r; rewrite <- !reprs_mem; split; intros [u Hu].
    assert (H := merge_find m p P u); unfold find, merge in *; simpl in *.
    rewrite MapFacts.map_o in Hu, H |-.
    destruct m[u] as [ ]_eqn; inversion Hu; subst; simpl in *.
    exists r0; split; auto.
    rewrite <- reprs_mem; exists u; rewrite Heqo; reflexivity.
    destruct Hu as [Hu Heq].
    rewrite <- reprs_mem in Hu; destruct Hu as [t' Ht']; exists t'.
    unfold merge, find in *; simpl.
    rewrite MapFacts.map_o; inversion Ht'; subst; simpl.
    constructor. rewrite H1; auto.
  Qed.
  Property reprs_merge' `{ThSpecs : @TheorySpecs Th} : 
    forall m p P r, r \In reprs (fst (merge' m p P)) <-> 
    (exists r', r' \In reprs m /\ subst p P r' === r).
  Proof.
    intros m p P r; rewrite <- !reprs_mem; split; intros [u Hu].
    assert (Hfind := merge'_find m p P u).
    assert (Hmem := merge'_mem m p P u).
    exists (m u); split.
    rewrite <- reprs_mem; exists u.
    unfold find, mem in *; simpl.
    rewrite !MapFacts.mem_find_b in Hmem.
    destruct m[u]; auto.
    inversion Hu; rewrite <- H in Hmem; discriminate.
    rewrite <- Hfind; unfold find.
    inversion Hu; auto.
    destruct Hu as [Hu Heq].
    rewrite <- reprs_mem in Hu; destruct Hu as [t' Ht']; exists t'.
    assert (Hfind := merge'_find m p P t').
    assert (Hmem := merge'_mem m p P t').
    unfold find, mem in *; simpl in *.
    rewrite !MapFacts.mem_find_b in Hmem.
    inversion Ht'; subst; rewrite <- H in *.
    destruct ((fst (merge' m p P)) [t']).
    constructor; rewrite Hfind, H1; auto.
    discriminate.  
  Qed.

  (* Cardinal *)
  Property num_classes_empty : num_classes empty = 0.
  Proof. 
    reflexivity.
  Qed.
  
  Require Import SetEqProperties.
  Property num_classes_add : forall m a, num_classes m <= num_classes (add m a).
  Proof.
    intros; unfold num_classes.
    apply subset_cardinal; apply subset_1; apply reprs_add_2.
  Qed.

  Lemma cardinal_map_le (f : R -> R) `{fm: Proper _ (_eq ==> _eq) f} :
    forall (S S' : set R),
    (forall r, r \In S' <-> (exists r', r' \In S /\ f r' === r)) ->
    SetInterface.cardinal S' <= SetInterface.cardinal S.
  Proof.
    intros S S' Hmerge; revert S' Hmerge; pattern S; 
      apply SetProperties.set_induction_bis; intros.
    (* - morphism *)
    rewrite <- H; apply H0; intro r; rewrite Hmerge.
    split; intros [r' Hr']; exists r'; (rewrite H || rewrite <- H); auto.
    (* - empty *)
    rewrite SetProperties.cardinal_1; auto.
    intros r Hr; rewrite Hmerge in Hr; destruct Hr as [r' [abs _]].
    contradiction (SetInterface.empty_1 abs).
    (* - add *)
    rewrite SetProperties.add_cardinal_2 by assumption.
    set (f' := fun y => f y == f x).
    assert (f'm : Proper (_eq ==> @Logic.eq bool) f').
    intros a b Heq; unfold f'.
    destruct (eq_dec (f a) (f x)); rewrite Heq in *;
      destruct (eq_dec (f b) (f x)); intuition.
    destruct (SetFacts.exists_dec s (f := f')).
    destruct Htrue as [u [Hu1 Hu2]]; unfold f' in Hu2.
    destruct (eq_dec (f u) (f x)); try discriminate; clear Hu2.
    constructor; apply H0; intro r; rewrite Hmerge.
    split; intros [r' [Hin Hsubst]].
    rewrite SetFacts.add_iff in Hin; destruct Hin.
    exists u; split; auto; rewrite H1, H2; exact Hsubst.
    exists r'; split; auto.
    exists r'; split; auto; apply SetInterface.add_2; auto.
    set (S'' := SetInterface.remove (f x) S').
    assert (cut : SetInterface.cardinal S'' <= SetInterface.cardinal s).
    apply H0; intro r; unfold S''; rewrite SetFacts.remove_iff, Hmerge.
    split.
    intros [[r' [Hin' Heq']] Hns].
    exists r'; split; auto; apply SetInterface.add_3 with x; auto.
    intro abs; rewrite abs in Hns; contradiction (Hns Heq').
    intros [r' [Hin' Heq']]; split.
    exists r'; split; auto; apply SetInterface.add_2; auto.
    intro abs; apply Hfalse; exists r'; split; auto.
    unfold f'; destruct (eq_dec (f r') (f x)); auto.
    contradiction H1; transitivity r; auto.
    rewrite <- remove_cardinal_1 with S' (f x).
    fold S''; auto with arith.
    apply SetInterface.mem_1; rewrite Hmerge; exists x; 
      split; auto; apply SetInterface.add_1; auto.
  Qed.
  Corollary num_classes_merge'  `{ThSpecs : @TheorySpecs Th} : 
    forall m p P, num_classes (fst (merge' m p P)) <= num_classes m.
  Proof.
    intros; unfold num_classes.
    apply (@cardinal_map_le (subst p P) _).
    apply reprs_merge'.
  Qed.

  Theorem num_classes_merge'_lt  `{ThSpecs : @TheorySpecs Th} : 
    forall m p P r r', r \In reprs m -> r' \In reprs m -> r =/= r' -> 
      subst p P r === subst p P r' -> 
        num_classes (fst (merge' m p P)) < num_classes m.
  Proof.
    intros; unfold num_classes.
    assert (Hmerge := reprs_merge' m p P).
    set (S := reprs m) in *; clearbody S.
    set (S' := reprs (fst (merge' m p P))) in *; clearbody S'.
    rewrite <- SetProperties.remove_cardinal_1 with (s := S) (x := r) by auto.
    apply le_lt_n_Sm.
    apply (@cardinal_map_le (subst p P) _).
    intro a; rewrite Hmerge; split; intros [a' [Hina Heqa]].
    destruct (eq_dec r a').
    exists r'; split.
    apply SetInterface.remove_2; auto.
    rewrite <- H3, H2 in Heqa; exact Heqa.
    exists a'; split; try apply SetInterface.remove_2; auto.
    exists a'; split; try apply SetInterface.remove_3 with r; auto.
  Qed.

  Property touched_spec :
    forall m p P t,
      List.In t (snd (merge_touched m p P)) <->
      (exists r, MapsTo t r m /\ r =/= subst p P r).
  Proof.
    intros m p P t0.
    apply (@MapFacts.fold_rec_bis _ _ _ _ _ _
      (fun (mvu : Map[term, R]) (mt : Map[term,R] * terms) =>
        List.In t0 (snd mt) <->
        exists r, MapsTo t0 r mvu /\ r =/= subst p P r)).
    (* - morphism *)
    intros; rewrite H0; split; intros [r Hr]; exists r;
      [rewrite <-H| rewrite H]; exact Hr.
    (* - empty *)
    simpl; split; intro. contradiction.
    destruct H as [r [Hr _]].
    rewrite MapFacts.empty_mapsto_iff in Hr; contradiction.
    (* - add *)
    intros; destruct a; simpl in *.
    destruct (eq_dec e (subst p P e)); simpl.
    rewrite H1; split; intros [r [Hr1 Hr2]].
    exists r; split; auto.
    rewrite MapFacts.add_neq_mapsto_iff; auto.
    intro abs; apply H0; exists r; rewrite abs; exact Hr1.
    exists r; split; auto.
    rewrite MapFacts.add_mapsto_iff in Hr1; auto.
    destruct Hr1 as [[? ?]|[? ?]]; subst; auto.
    contradiction (Hr2 H2).
    rewrite H1; clear H1; split; intro.
    destruct H1 as [?|[r [Hr1 Hr2]]]; subst.
    exists e; split; auto; apply add_1; auto.
    exists r; split; auto.
    apply add_2; auto; intro abs; apply H0;
      rewrite abs; exists r; auto.
    destruct H1 as [r [Hr1 Hr2]].
    rewrite MapFacts.add_mapsto_iff in Hr1; destruct Hr1.
    left; exact (proj1 H1).
    right; exists r; tauto.
  Qed.

  Property merge'_touched_spec :
    forall m p P t,
      List.In t (snd (merge' m p P)) <->
      (mem m t = true /\ m t =/= subst p P (m t)).
  Proof.
    intros m p P t0; unfold merge'.
    assert (Htouched := touched_spec m p P t0).
    destruct (merge_touched m p P) as [mr tr]; simpl in *.
    rewrite Htouched; clear Htouched; unfold mem, find; simpl.
    rewrite MapFacts.mem_find_b.
    destruct (m[t0]) as [ ]_eqn; split; intro.
    split; auto; destruct H as [r' [Hr'1 Hr'2]].
    rewrite MapFacts.find_mapsto_iff in Hr'1.
    rewrite Heqo in Hr'1; inversion Hr'1; subst; auto.
    exists r; split; auto.
    apply find_2; auto. tauto.
    destruct H as [r' [Hr'1 _]].
    rewrite MapFacts.find_mapsto_iff, Heqo in Hr'1; discriminate.
    destruct H; discriminate.
  Qed.
End WithTheorySpecs.

Global Opaque t empty find add merge merge_touched
  merge' congruent range reprs num_classes.