Require Import Maps Sets SetProperties.
Require Import Theory TermUtils.

Set Implicit Arguments.
Unset Strict Implicit.

Section WithTheory.
  Context `{Th : Theory}.
  
  SubClass t := Map[R, set term].

  Definition empty : t := [].

  Definition find (m : t) (r : R) : set term :=
    match m[r] with
      | Some r => r
      | None => {}
    end.
  Global Coercion find : t >-> Funclass.

  Definition merge (m : t) (p P : R) : t :=
    match m[p] with
      | None => m
      | Some usedp =>
        let lP := leaves P in
          List.fold_left (fun m l => insert l usedp (union usedp) m) lP
          (MapInterface.remove p m)
    end.

  Definition add (m : t) (fa : term) (la : list R) : t :=
    List.fold_left (fun m l => insert l {fa} (add fa) m) la m.

  Definition using_all (m : t) (lvs : list R) : set term :=
    match lvs with
      | nil => {}
      | x::ls =>
        List.fold_left (fun acc y => inter acc (m y)) ls (m x)
    end.

  Definition terms_of (m : t) : set term :=
    MapInterface.fold (fun _ v acc => v ++ acc) m {}.
End WithTheory.

Section WithTheorySpecs.
  Context `{Th: Theory}.

  (* About empty *)
  Property empty_find : forall r, empty r = {}.
  Proof.
    intros; unfold empty, find; rewrite MapFacts.empty_o; reflexivity.
  Qed.

  (* About merge *)
  Fixpoint in_list (r : R) (l : list R) : bool := 
    match l with
      | nil => false
      | r'::q => if r == r' then true else in_list r q
    end.
  Property in_list_rev_iff : forall r l, in_list r l = in_list r (rev l).
  Proof.
    intros r; induction l; simpl.
    reflexivity.
    destruct (eq_dec r a); simpl.
    clear IHl; pattern (rev l); apply list_ind; simpl; intros.
    destruct (eq_dec r a); auto; order.
    destruct (eq_dec r a0); auto.
    rewrite IHl; clear IHl; pattern (rev l); apply list_ind; simpl; intros.
    destruct (eq_dec r a); auto; order.
    rewrite H0; auto.
  Qed.

  Property insert_eq_o :
    forall (k : R) (d : set term) f m k', 
      k === k' -> (insert k d f m)[k'] = 
      match m[k'] with Some d' => Some (f d') | None => Some d end.
  Proof.
    intros; destruct (m[k']) as [d'|]_eqn:Hk'; apply find_1.
    apply insert_1; [exact H | exact (find_2 Hk')].
    apply insert_2; auto; rewrite MapFacts.not_find_in_iff; exact Hk'.
  Qed.
  Property insert_neq_o :
    forall (k : R) (d : set term) f m k', 
      k =/= k' -> (insert k d f m)[k'] = m[k'].
  Proof.
    intros; destruct (m[k']) as [d'|]_eqn:Hk'.
    apply find_1; apply insert_3; [exact H | exact (find_2 Hk')].
    rewrite <- MapFacts.not_find_in_iff in Hk' |- *; 
      intros [d' abs]; apply Hk'; exists d'; exact (insert_4 H abs).
  Qed.

  Property merge_find : forall m p P r,
    in_list p (leaves P) = false ->
    (merge m p P) r [=]
    (match m[p] with
       | None => m r
       | Some usedp =>
         if r == p then {} else 
           if in_list r (leaves P) then
             usedp ++ m r
             else m r
     end).
  Proof.
    intros; unfold merge, find.
    destruct (m[p]) as [usedp|]_eqn:Hp; [|reflexivity].
    set (f (l : R) m0 := insert l usedp (union usedp) m0).
    match goal with
      | |- context G [fun m0 l => insert l usedp (union usedp) m0] =>
        let t := context G [fun m0 l => f l m0] in change t
    end.
    rewrite <- fold_left_rev_right, in_list_rev_iff in *; revert H.
    pattern (rev (leaves P)); apply list_ind; simpl; intros.
    (* - nil *)
    destruct (eq_dec r p).
    rewrite MapFacts.remove_eq_o; auto; reflexivity.
    rewrite MapFacts.remove_neq_o; try reflexivity; intro abs; order.
    (* - cons *)
    set (M := fold_right f (MapInterface.remove p m) l) in *; clearbody M.
    unfold f in *; clear f.
    destruct M[r] as [usedr|]_eqn:Hr.
    destruct (eq_dec r a) as [Heqa | Hneqa].
    rewrite insert_eq_o; auto; rewrite Hr; simpl.
    destruct (eq_dec r p) as [Heqp | Hneqp].
    destruct (eq_dec p a); [discriminate | order].
    destruct (eq_dec p a); [order | rewrite (H H0)].
    destruct (in_list r l).
    rewrite <-union_assoc; apply union_m; try reflexivity.
    apply union_subset_equal; reflexivity.
    reflexivity.
    rewrite insert_neq_o by (intro abs; apply Hneqa; auto).
    rewrite Hr; apply H.
    destruct (eq_dec p a); auto; discriminate.
    destruct (eq_dec r a) as [Heqa | Hneqa].
    rewrite insert_eq_o; auto; rewrite Hr; simpl.
    destruct (eq_dec r p) as [Heqp | Hneqp].
    destruct (eq_dec p a); [discriminate | order].
    destruct (eq_dec p a); [order |].
    assert (H' := H H0); clear H H0.
    destruct (in_list r l).
    cut (usedp [=] {}).
    intro cut; rewrite <- H', cut; reflexivity.
    apply empty_is_empty_1; intros z Hz; apply empty_1 with z.
    rewrite H'; apply union_2; exact Hz.
    rewrite <- H'; rewrite empty_union_2; [reflexivity | 
      intros ? abs; contradiction (empty_1 abs)].
    rewrite insert_neq_o by (intro abs; apply Hneqa; auto).
    rewrite Hr; apply H.
    destruct (eq_dec p a); auto; discriminate.
  Qed.
    
  (* About terms_of *)
  Property terms_of_iff :
    forall m t, t \In terms_of m <-> exists r, t \In m r.
  Proof.
    intro m; unfold terms_of, find.
    apply (@MapFacts.fold_rec_bis _ _ _ _ _ _
      (fun (mvu : t) f => forall t, 
        t \In f <-> exists r, t \In 
          match mvu[r] with | Some r0 => r0 | None => {} end)); simpl; intros.
    (* - morphism *)
    rewrite H0; split; intros [r Hr]; exists r; 
      [rewrite <- H | rewrite H]; exact Hr.
    (* - empty *)
    split; intro abs.
    contradiction (empty_1 abs).
    destruct abs as [r Hr]; rewrite MapFacts.empty_o in Hr; auto.
    (* - add *)
    rewrite union_iff, H1; clear H1; split.
    intros [Ht | [r Hr]].
    exists k; rewrite MapFacts.add_eq_o; auto.
    exists r; rewrite MapFacts.add_neq_o; auto.
    intro abs; apply H0; rewrite abs.
    destruct (m'[r]) as [ ]_eqn.
    exists s; apply find_2; auto.
    contradiction (empty_1 Hr).
    intros [r Hr].
    destruct (eq_dec k r); [left | right].
    rewrite MapFacts.add_eq_o in Hr; auto.
    exists r; rewrite MapFacts.add_neq_o in Hr; auto.
  Qed.

  Property terms_of_empty : terms_of empty = {}.
  Proof. 
    reflexivity.
  Qed.

  Property terms_of_find : forall (m : t) r, m r [<=] terms_of m.
  Proof.
    intros; intros a Ha; rewrite terms_of_iff; exists r; auto.
  Qed.

  Remark InA_in_list : forall r l, reflects (InA _eq r l) (in_list r l).
  Proof.
    intro r; induction l; simpl.
    constructor; intro abs; inversion abs.
    inversion_clear IHl.
    destruct (r == a); constructor; constructor 2; exact Htrue.
    destruct (eq_dec r a); constructor.
    constructor; auto. intro abs; inversion_clear abs; auto.
  Qed.
  Property terms_of_merge `{ThSpecs: @TheorySpecs Th} : 
    forall m p P, ~InA _eq p (leaves P) -> 
      terms_of (merge m p P) [=] terms_of m.
  Proof.
    intros; intro a; rewrite 2terms_of_iff.
    assert (H' : in_list p (leaves P) = false)
      by (destruct (InA_in_list p (leaves P)); intuition).
    split; intros [r Hr].
    rewrite merge_find in Hr by assumption.
    destruct m[p] as [usedp|]_eqn:Hp.
    destruct (eq_dec r p) as [Heqp | Hneqp].
    contradiction (empty_1 Hr).
    destruct (in_list r (leaves P)).
    rewrite union_iff in Hr; destruct Hr; [exists p | exists r]; auto.
    unfold find; rewrite Hp; exact H0.
    exists r; auto.
    exists r; auto.
    destruct m[p] as [usedp|]_eqn:Hp.
    destruct (eq_dec r p) as [Heqp | Hneqp].
    assert (Hnot_empty := leaves_not_empty (r:=P)).
    destruct (leaves P) as [|l q]_eqn; try congruence.
    exists l; rewrite merge_find by congruence; rewrite Hp.
    destruct (eq_dec l p).
    contradiction H; constructor; auto.
    destruct (InA_in_list l (leaves P)).
    apply union_2; unfold find in Hr; rewrite <- Heqp in Hp;
      rewrite Hp in Hr; auto.
    contradiction Hfalse; rewrite Heql; constructor; auto.
    exists r; rewrite merge_find by assumption; rewrite Hp.
    destruct (eq_dec r p); [order |].
    destruct (in_list r (leaves P)); [apply union_3 |]; exact Hr.
    exists r; rewrite merge_find by assumption; rewrite Hp; exact Hr.
  Qed.
End WithTheorySpecs.
Global Opaque t empty find merge add using_all terms_of.
