Require Export Containers.Maps QArith.
Require Import Containers.MapFacts Containers.OrderedTypeEx.
Require Import Theory.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Module RAW.
(** This file provides an implementation of polynoms
   of degree 1 with rational coefficients over 
   variables in an [UsualOrderedType]. *)
Section WithVars.
  Variable vars : Type.
  Context `{vars_OT : OrderedType vars}.

  (** A polynom is the constant coefficient plus the sum of
     monoms, encoded as a map from terms to rationals. *)
  Definition poly := (Q * Map[vars, Q])%type.

  (** Constant polynoms 0 and 1, and z for all z *)
  Definition P0 : poly := (0, []).
  Definition P1 : poly := (1, []).
  Definition Pz (z : Z) : poly := (z#1, []).
  Definition Pq (q : Q) : poly := (q, []).
  
  Definition embed (v : vars) : poly := (0, [][v <- 1]).

  (** Constructors *)
  Definition mult (c : Q) (p : poly) : poly :=
    if (c == 0)%compare then P0 else (c*(fst p), map (Qmult c) (snd p)).

  Definition add_const (c : Q) (p : poly) : poly :=
    (fst p + c, snd p).
  Definition cancel (v : vars) (p : poly) : poly :=
    (fst p, remove v (snd p)).

  Definition addk_m (p1 : Map[vars,Q]) (k : Q) (p2 : Map[vars,Q]) : 
    Map[vars,Q]:=
    map2 (fun oc1 oc2 =>
      match oc1, oc2 with
        | None, None => None
        | Some q1, Some q2 => 
          let q := q1 + k * q2 in 
            if (q == 0)%compare then None else Some q
        | Some q1, None => Some q1
        | None, Some q2 => Some (k * q2)
      end) p1 p2.
  Definition addk (p1 : poly) (k : Q) (p2 : poly) : poly :=
    if (k==0)%compare then p1 
    else
      (fst p1 + k * fst p2, addk_m (snd p1) k (snd p2)).
  Definition add_monome (t : vars) (coef : Q) (p : poly) : poly :=
    if (coef==0)%compare then p
      else (fst p, addk_m (snd p) coef [][t <- 1]).

  Definition add (p1 p2 : poly) : poly := addk p1 1 p2.
  Definition sub (p1 p2 : poly) : poly := addk p1 (-(1)) p2.
  Definition div (c : Q) (p : poly) : poly := mult (Qinv c) p.

  (** Access to coefficients and coef-wise equivalence *)
  Definition coef_of (p : poly) (v : option vars) : Q :=
    match v with 
      | Some v =>
        match (snd p)[v] with Some q => q | None => 0 end
      | None =>
        fst p
    end.
  Global Coercion coef_of : poly >-> Funclass.

  Definition equiv (p1 p2 : poly) :=
    forall t, p1 t === p2 t.
  
  Global Instance coef_of_equiv : 
    Proper (equiv ==> _eq ==> _eq) coef_of.
  Proof.
    repeat intro.
    inversion H0; subst.
    exact (H None).
    transitivity (x (Some a')); simpl.
    assert (Z : (snd x)[a] === (snd x)[a']) by (rewrite H1; reflexivity).
    unfold coef_of; destruct Z; auto; reflexivity.
    exact (H (Some a')).
  Qed.
  Global Instance equiv_Reflexive : Reflexive equiv.
  Proof. repeat intro; reflexivity. Qed.
  Global Instance equiv_Symmetric : Symmetric equiv.
  Proof. repeat intro; rewrite H; reflexivity. Qed.
  Global Instance equiv_Transitive : Transitive equiv.
  Proof. repeat intro; rewrite H, H0; reflexivity. Qed.

  (** Polynoms as an OrderedType :
     2 polynoms are equal iff their variables have equal coefficients,
     including those with mapped to zeroes. This low-level equality is
     faster to check than [equiv] and convenient for computations.
     *)
  Definition MapQ_OT : OrderedType (Map[vars, Q]) :=
    (@SOT_as_OT _ _ FMap_SpecificOrderedType).
  Existing Instance MapQ_OT.
  Definition poly_OT : OrderedType poly :=
    prod_OrderedType _ MapQ_OT.
  Existing Instance poly_OT.

  (** Morphisms for this notion of equality *)
  Opaque poly_OT.
  Local Instance find_m :
    Proper (_eq ==> _eq ==> _eq) (@find vars vars_OT _ Q).
  Proof.
    intros x y H m m' Heq.
    rewrite H.
    destruct (m[y]) as [qy|]_eqn:Hy.
    apply find_2 in Hy.
    destruct (proj1 (Heq y qy)) as [q'y [Hqq' Hq'y]].
    exists qy; split; auto.
    apply find_1 in Hq'y; rewrite Hq'y; constructor; assumption.
    destruct (m'[y]) as [q'y|]_eqn:Hy'.
    apply find_2 in Hy'.
    destruct (proj2 (Heq y q'y)) as [qy [Hqq' Hqy]].
    exists q'y; split; auto.
    apply find_1 in Hqy; rewrite Hqy in Hy; discriminate.
    constructor.
  Qed.
  Local Instance In_m : 
    Proper (_eq ==> _eq ==> iff) (@In vars vars_OT _ Q).
  Proof.
    intros k k' Hk m m' Hm; rewrite !in_find_iff in *.
    assert (H := find_m Hk Hm).
    inversion H; intuition congruence.
  Qed.

  Local Instance add_m :
    Proper (_eq ==> _eq ==> _eq ==> _eq) 
    (@MapInterface.add vars vars_OT _ Q).
  Proof.
    intros k k' Hk q q' Hq m m' Heq.
    intros k'' v; split; intros [v' [Hvv' Hv]].
    rewrite add_mapsto_iff in Hv; destruct Hv as [Hv | Hv]; destruct Hv.
    subst; exists q'; split. transitivity v'; assumption. 
    apply add_1; auto; transitivity k; auto.
    assert (R := find_m (reflexivity k'') Heq).
    apply find_1 in H0; rewrite H0 in R; inversion R; subst; clear R.
    rewrite Hk in H; exists a'; split. transitivity v'; auto.
    apply add_2; auto; apply find_2; auto.
    rewrite add_mapsto_iff in Hv; destruct Hv as [Hv | Hv]; destruct Hv.
    subst; exists q; split. transitivity v'; auto.
    apply add_1; auto; transitivity k'; auto.
    assert (R := find_m (reflexivity k'') Heq).
    apply find_1 in H0; rewrite H0 in R; inversion R; subst; clear R.
    rewrite <- Hk in H; exists a; split. transitivity v'; auto.
    apply add_2; auto; apply find_2; auto.
  Qed.
  Local Instance remove_m :
    Proper (_eq ==> _eq ==> _eq) 
    (@MapInterface.remove vars vars_OT _ Q).
  Proof.
    intros k k' Hk m m' Heq.
    intros k'' v; split; intros [v' [Hvv' Hv]].
    rewrite remove_mapsto_iff in Hv; destruct Hv; rewrite Hk in H.
    assert (R := find_m (reflexivity k'') Heq).
    apply find_1 in H0; rewrite H0 in R; inversion R; subst; clear R.
    exists a'; split. transitivity v'; auto. 
    apply remove_2; auto; apply find_2; auto.
    rewrite remove_mapsto_iff in Hv; destruct Hv; rewrite <- Hk in H.
    assert (R := find_m (reflexivity k'') Heq).
    apply find_1 in H0; rewrite H0 in R; inversion R; subst; clear R.
    exists a; split. transitivity v'; auto. 
    apply remove_2; auto; apply find_2; auto.
  Qed.
  
  Local Instance elements_m :
    Proper (_eq ==> _eq) (@elements vars vars_OT _ Q).
  Proof.
    intros m m' Hm.
    assert (H := @elements_mapsto_iff _ _ _ _ Q m).
    assert (Hsort := @elements_3 _ _ _ _ Q m).
    assert (H' := @elements_mapsto_iff _ _ _ _ Q m').
    assert (Hsort' := @elements_3 _ _ _ _ Q m').
    assert (Cut : 
      forall k v, 
        (exists v', v === v' /\ InA eq_key_elt (k, v') (elements m)) <->
        (exists v', v === v' /\ InA eq_key_elt (k, v') (elements m'))).
    intros k v; split; intros [v' [Hvv' Hv']].
    destruct (proj1 (Hm k v')) as [v'' [Hvv'' Hv'']].
    exists v'; split; auto; rewrite H; assumption.
    exists v''; split. transitivity v'; auto. rewrite <- H'; assumption.
    destruct (proj2 (Hm k v')) as [v'' [Hvv'' Hv'']].
    exists v'; split; auto; rewrite H'; assumption.
    exists v''; split. transitivity v'; auto. rewrite <- H; assumption.
    clear H H' Hm.
    revert Hsort Hsort' Cut.
    generalize (elements m) (elements m'); clear m m'.
    induction l; intro l'; destruct l'; intros Hsort Hsort' Cut.
    constructor.
    destruct p as [a b]; destruct (proj2 (Cut a b)) as [? [_ abs]].
    exists b; split; auto. inversion abs.
    destruct a as [c d]; destruct (proj1 (Cut c d)) as [? [_ abs]].
    exists d; split; auto. inversion abs.
    inversion_clear Hsort; inversion_clear Hsort'.
    assert (cutsort : forall l (x a : vars * Q), sort lt_key l ->
      lelistA lt_key a l -> InA eq_key_elt x l -> lt_key a x).
    apply SortA_InfA_InA.
    apply KeyOrderedType.eqke_Equiv.
    apply KeyOrderedType.ltk_SO.
    intros (w,z)(w',z')(Hw,Hz) (w1,z1)(w1',z1')(Hw1,Hz1); simpl in *.
    unfold lt_key, KeyOrderedType.ltk; simpl; subst; intuition order.
    destruct a as [k v]; destruct p as [a b].
    assert (Heq : k === a /\ v === b).
    destruct (proj1 (Cut k v)) as [k'' [Heq'' Hin'']]; [exists v; split; auto|].
    inversion Hin''; subst; clear Hin''.
    inversion_clear H4; simpl in *; subst. constructor; auto.
    destruct (proj2 (Cut a b)) as [a' [Heq' Hin']]; [exists b; split; auto|].
    inversion Hin'; subst; clear Hin'.
    inversion_clear H5; simpl in *; subst; constructor; auto.
    assert (R := cutsort _ _ _ H H0 H5).
    assert (R' := cutsort _ _ _ H1 H2 H4).
    unfold lt_key, KeyOrderedType.ltk in R, R'; simpl in R, R'.
    contradiction (lt_not_gt R R').
    constructor.
    constructor; destruct Heq; auto.
    apply IHl; try assumption.
    intros g h; split; intros [h' [Hh' Hinh']].
    destruct (proj1 (Cut g h')) as [h'' [Hh'' Hinh'']]; 
      [exists h'; split; auto|].
    inversion Hinh''; auto; subst.
    2:(exists h''; split; [transitivity h'; assumption | auto]).
    inversion_clear H4; simpl in *; subst.
    assert (R := cutsort _ _ _ H H0 Hinh').
    compute in R; rewrite H3 in R; contradiction (lt_not_eq R (proj1 Heq)).
    destruct (proj2 (Cut g h')) as [h'' [Hh'' Hinh'']]; 
      [exists h'; split; auto|].
    inversion Hinh''; auto; subst.
    2:(exists h''; split; [transitivity h'; assumption | auto]).
    inversion_clear H4; simpl in *; subst.
    assert (R := cutsort _ _ _ H1 H2 Hinh').
    compute in R; contradiction (lt_not_eq R); rewrite H3; symmetry; tauto.
  Qed.
  Local Instance fold_m `{A_OT : OrderedType A} :
    Proper ((_eq ==> _eq ==> _eq ==> _eq) ==> _eq ==> _eq ==> _eq)
    (@fold vars vars_OT _ Q A).
  Proof.
    intros f f' Hf m m' Hm i i' Hi.
    rewrite !fold_1; assert (Heqm := elements_m  Hm); clear Hm.
    revert i i' Hi Heqm; generalize (elements m) (elements m'); clear m m'.
    induction l; intros l'; destruct l'; intros; simpl in *.
    assumption.
    inversion Heqm.
    inversion Heqm.
    inversion Heqm; subst; simpl in *.
    destruct H2; subst; simpl in *.
    apply IHl; auto. apply Hf; auto.
  Qed.
  Local Instance cardinal_m :
    Proper (_eq ==> _eq) (@cardinal vars vars_OT _ Q).
  Proof.
    repeat intro; rewrite 2cardinal_fold.
    apply fold_m; auto.
    repeat intro; congruence.
  Qed.

  Local Instance map2_m :
    Proper ((_eq ==> _eq ==> _eq) ==> _eq ==> _eq ==> _eq)
    (@map2 vars vars_OT _ Q Q Q).
  Proof.
    intros f f' Hf m1 m1' Hm1 m2 m2' Hm2.
    intros k v.
    assert (Heq : f (m1[k]) (m2[k]) === f' (m1'[k]) (m2'[k])).
    refine (Hf (m1[k]) (m1'[k]) _ (m2[k]) (m2'[k]) _); 
      try (apply find_m; auto).
    split; intros [z [Hzv Hz]].
    cut (In k m1 \/ In k m2); [intro cut|].
    apply find_1 in Hz; rewrite map2_1 in Hz; auto.
    rewrite Hz in Heq; inversion Heq; subst.
    exists a'; split. transitivity z; auto. apply find_2.
    rewrite Hm1, Hm2 in cut; rewrite map2_1; auto.
    eapply map2_2; exists z; apply Hz.
    cut (In k m1' \/ In k m2'); [intro cut|].
    apply find_1 in Hz; rewrite map2_1 in Hz; auto.
    rewrite Hz in Heq; inversion Heq; subst.
    exists a; split. transitivity z; auto. apply find_2.
    rewrite <- Hm1, <- Hm2 in cut; rewrite map2_1; auto.
    eapply map2_2; exists z; apply Hz.
  Qed.

  Local Instance is_compare_m `{OrderedType A} :
    Proper (_eq ==> _eq ==> @Logic.eq _ ==> @Logic.eq _) is_compare.
  Proof.
    repeat intro; subst; unfold is_compare.
    destruct (compare_dec x x0); destruct (compare_dec y y0); 
      auto; solve [order].
  Qed.
  
  Local Instance mult_m : Proper (_eq ==> _eq ==> _eq) mult.
  Proof.
    repeat intro; unfold mult.
    inversion_clear H0; simpl.
    destruct (eq_dec x 0) as [Hc|Hc]; rewrite H in Hc.
    unfold is_compare; rewrite (elim_compare_eq Hc).
    reflexivity.
    destruct (eq_dec y 0); try contradiction.
    constructor.
    rewrite H, H1; reflexivity.
    unfold _eq; simpl.
    repeat intro; split; intros [q [Hq Hmap]].
    rewrite map_mapsto_iff in Hmap; 
      destruct Hmap as [qb [Hqx Hqb]].
    destruct (proj1 (H2 k qb)) as [qd [Hqd Hmapd]]; [exists qb; split; auto|].
    exists (y * qd); split. rewrite Hq, Hqx, Hqd, H; reflexivity.
    rewrite map_mapsto_iff; exists qd; split; auto.
    rewrite map_mapsto_iff in Hmap; 
      destruct Hmap as [qd [Hqy Hqd]].
    destruct (proj2 (H2 k qd)) as [qb [Hqx Hqb]]; [exists qd; split; auto|].
    exists (x * qb); split. rewrite Hq, Hqy, Hqx, H; reflexivity.
    rewrite map_mapsto_iff; exists qb; split; auto.
  Qed.
  
  Local Instance add_const_m : 
    Proper (_eq ==> _eq ==> _eq) add_const.
  Proof.
    repeat intro; unfold add_const.
    inversion_clear H0; simpl; constructor; auto.
    rewrite H1, H; reflexivity.
  Qed.
  Local Instance cancel_m : 
    Proper (_eq ==> _eq ==> _eq) cancel.
  Proof.
    repeat intro; unfold cancel.
    inversion_clear H0; simpl; constructor; auto.
    rewrite H2, H; reflexivity.
  Qed.

  Local Instance addk_m_m : 
    Proper (_eq ==> _eq ==> _eq ==> _eq) addk_m.
  Proof.
    intros p1 p1' Hp1 k k' Hk p2 p2' Hp2; unfold addk_m.
    apply map2_m; auto.
    repeat intro.
    inversion H; inversion H0; subst.
    constructor.
    constructor; rewrite Hk, H3; reflexivity.
    assumption.
    inversion H0; inversion H; subst.
    rewrite is_compare_m with (a+k*a0) (a'+k'*a'0) 0 0 Eq Eq; auto.
    destruct (eq_dec (a'+k'*a'0) 0); constructor.
    rewrite H1, Hk, H5; reflexivity.
    rewrite H1, Hk, H5; reflexivity.
  Qed.
  Local Instance addk_morphism : 
    Proper (_eq ==> _eq ==> _eq ==> _eq) addk.
  Proof.
    intros p1 p1' Hp1 k k' Hk p2 p2' Hp2; unfold addk.
    rewrite is_compare_m with k k' 0 0 Eq Eq; auto.
    destruct (eq_dec k' 0) as [E|N].
    exact Hp1.
    inversion Hp1; inversion Hp2; subst; simpl; constructor.
    rewrite H3, Hk, H; reflexivity.
    apply addk_m_m; auto.
  Qed.

  Local Instance embed_m : Proper (_eq ==> _eq) embed.
  Proof.
    repeat intro; unfold embed.
    constructor; auto; rewrite H; reflexivity.
  Qed.
  Local Instance add_monome_m :
    Proper (_eq ==> _eq ==> _eq ==> _eq) add_monome.
  Proof.
    intros p1 p1' Hp1 k k' Hk p2 p2' Hp2; unfold add_monome.
    rewrite is_compare_m with k k' 0 0 Eq Eq; auto.
    destruct (eq_dec k' 0) as [E|N].
    exact Hp2.
    inversion Hp2; subst; simpl; constructor; auto.
    apply addk_m_m; auto; apply add_m; auto.
  Qed.

  Local Instance padd_m : Proper (_eq ==> _eq ==> _eq) add.
  Proof.
    repeat intro; unfold add; apply addk_morphism; auto.
  Qed.
  Local Instance sub_m : Proper (_eq ==> _eq ==> _eq) sub.
  Proof.
    repeat intro; unfold sub; apply addk_morphism; auto.
  Qed.
  Local Instance div_m : Proper (_eq ==> _eq ==> _eq) div.
  Proof.
    repeat intro; unfold div; rewrite H, H0; reflexivity.
  Qed.

  Global Instance coef_of_m : 
    Proper (_eq ==> _eq ==> _eq) coef_of.
  Proof.
    repeat intro; unfold coef_of.
    inversion_clear H; subst; simpl;
      inversion_clear H0; subst; simpl; auto.
    assert (R := find_m H H2).
    destruct R; auto; reflexivity.
  Qed.
  Global Instance eq_equiv : 
    Proper (_eq ==> _eq ==> iff) equiv.
  Proof.
    repeat intro; unfold equiv; split; intros H' t;
      generalize (H' t); clear H'; intro H'.
    rewrite <- H, <- H0; exact H'.
    rewrite H, H0; exact H'.
  Qed.
    
  (** Properties and specs, in terms of === *)
  CoInductive is_mult_of (c : Q) (t : vars) (v : Q) (m : Map[vars, Q]) : Prop :=
  | is_mult_intro :
    forall q, c =/= 0 -> v = c * q -> MapsTo t q m -> is_mult_of c t v m.
  CoInductive mult_spec (c : Q) (p : poly) : poly -> Prop :=
  | mult_spec_intro : 
    forall rc rm
      (Hmult_coef : rc === c * fst p)
      (Hmult_poly : forall t v, MapsTo t v rm <-> is_mult_of c t v (snd p)),
      mult_spec c p (rc, rm).
  Property mult_dec : forall c p, mult_spec c p (mult c p).
  Proof.
    intros; unfold mult.
    destruct (eq_dec c 0) as [Heq|Hneq]; constructor.
    rewrite Heq; reflexivity.
    intros t v; split; intro.
    rewrite empty_mapsto_iff in H; contradiction.
    inversion H; contradiction.
    reflexivity.
    intros t v; split; intro. 
    rewrite map_mapsto_iff in H; destruct H.
    exists x; tauto.
    inversion H; rewrite map_mapsto_iff.
    exists q; tauto.
  Qed.

  CoInductive is_addk_of (v : vars) (q : Q) m1 k (m2 : Map[vars, Q]) : Prop :=
  | is_addk_of_both :
    forall q1 q2, MapsTo v q1 m1 -> MapsTo v q2 m2 ->
      q = q1 + k * q2 -> q =/= 0 -> is_addk_of v q m1 k m2
  | is_addk_of_1 :
    MapsTo v q m1 -> ~In v m2 -> is_addk_of v q m1 k m2
  | is_addk_of_2 :
    forall q2, q = k * q2 -> MapsTo v q2 m2 -> ~In v m1 -> 
      is_addk_of v q m1 k m2.
  CoInductive addk_m_spec (p1 : Map[vars,Q]) (k : Q) (p2 : Map[vars,Q]) :
    Map[vars,Q] -> Prop :=
  | addk_m_spec_intro : 
    forall rm
      (Haddk_poly : forall v q, MapsTo v q rm <-> is_addk_of v q p1 k p2),
      addk_m_spec p1 k p2 rm.
  Property addk_m_dec : forall p1 k p2, addk_m_spec p1 k p2 (addk_m p1 k p2).
  Proof.
    intros; unfold addk_m.
    constructor; auto; intros v q.
    rewrite find_mapsto_iff, map2_1bis; auto.
    split; intro H.
    destruct (p1[v]) as [q1|]_eqn:H1;
      destruct (p2[v]) as [q2|]_eqn:H2; auto.
    destruct (eq_dec (q1+k*q2) 0); inversion H; subst.
    constructor 1 with q1 q2; try (apply find_2; auto); eauto using find_2. (* TODO: eauto seul marche pas *)
    inversion H; subst; constructor 2; try (apply find_2; auto); auto using find_2.
    rewrite not_find_in_iff; assumption.
    inversion H; subst; constructor 3 with q2; try (apply find_2; auto); auto using find_2.
    rewrite not_find_in_iff; assumption.
    discriminate.
    inversion H; subst.
    rewrite (find_1 H0), (find_1 H1).
    destruct (eq_dec (q1 + k * q2) 0); auto. 
    contradiction H3; transitivity (q1 + k * q2); auto.
    rewrite not_find_in_iff in H1; rewrite (find_1 H0), H1; reflexivity.
    rewrite not_find_in_iff in H2; rewrite (find_1 H1), H2; reflexivity.
  Qed.

  CoInductive addk_spec (p1 : poly) (k : Q) (p2 : poly) : poly -> Prop :=
  | addk_spec_0 : 
    forall (Hknul : k === 0), addk_spec p1 k p2 p1
  | addk_spec_intro : 
    forall rm (Hk : k =/= 0)
      (Haddk_poly : forall v q, MapsTo v q rm <-> 
        is_addk_of v q (snd p1) k (snd p2)),
      addk_spec p1 k p2 (fst p1 + k * fst p2, rm).
  Property addk_dec : forall p1 k p2, addk_spec p1 k p2 (addk p1 k p2).
  Proof.
    intros; unfold addk.
    destruct (eq_dec k 0).
    constructor; auto.
    destruct (addk_m_dec (snd p1) k (snd p2)).
    constructor 2; auto.
  Qed.  

  CoInductive is_add_monome_of (v : vars) (q : Q) 
    (t : vars) (c : Q) (m : Map[vars, Q]) : Prop :=
  | is_add_monome_adjust :
    forall qt, v === t -> MapsTo t qt m ->
      q = qt + c * 1 -> q =/= 0 -> is_add_monome_of v q t c m
  | is_add_monome_diff :
    v =/= t -> MapsTo v q m -> is_add_monome_of v q t c m
  | is_add_monome_add :
    v === t -> q = c * 1 -> ~In v m -> is_add_monome_of v q t c m.
  CoInductive add_monome_spec (t : vars) (c : Q) (p : poly) : poly -> Prop :=
  | add_monome_spec_0 : 
    forall (Hcnul : c === 0), add_monome_spec t c p p
  | add_monome_spec_intro :
    forall rm (Hc : c =/= 0)
      (Hadd_monome_poly :
        forall k v, MapsTo k v rm <-> is_add_monome_of k v t c (snd p)),
      add_monome_spec t c p (fst p, rm).
  Property add_monome_dec : forall t c p,
    add_monome_spec t c p (add_monome t c p).
  Proof.
    intros; unfold add_monome.
    destruct (eq_dec c 0) as [E|N]; constructor; auto.
    destruct (addk_m_dec (snd p) c ([][t <- 1])).
    intros; rewrite Haddk_poly.
    intros; split; simpl; intro H; inversion H; subst; clear H.
    rewrite add_mapsto_iff in H1; destruct H1.
    destruct H; subst; rewrite <- H in H0.
    constructor 1 with q1; auto.
    rewrite empty_mapsto_iff in H; destruct H; contradiction.
    rewrite add_in_iff, empty_in_iff in H1.
    constructor 2; auto; intro abs; apply H1; left; auto.
    rewrite add_mapsto_iff in H1; destruct H1.
    destruct H; subst. constructor 3; auto.
    rewrite empty_mapsto_iff in H; destruct H; contradiction.
    rewrite <- H0 in H1.
    constructor 1 with qt 1; auto. rewrite add_mapsto_iff; intuition.
    constructor 2; auto. rewrite add_in_iff, empty_in_iff; intuition.
    constructor 3 with 1; auto.
    rewrite add_mapsto_iff, empty_mapsto_iff; intuition.
  Qed.

  CoInductive add_spec (p1 p2 : poly) : poly -> Prop :=
  | add_spec_intro :
    forall rm
      (Hadd_poly : forall k v,
        MapsTo k v rm <-> is_addk_of k v (snd p1) 1 (snd p2)),
      add_spec p1 p2 (fst p1 + 1 * fst p2, rm).
  Theorem add_dec : forall p1 p2, add_spec p1 p2 (add p1 p2).
  Proof.
    intros p1 p2; unfold add; destruct (addk_dec p1 1 p2).
    discriminate.
    constructor; intros; simpl; auto.
  Qed.

  CoInductive sub_spec (p1 p2 : poly) : poly -> Prop :=
  | sub_spec_intro :
    forall rm
      (Hsub_poly : forall k v,
        MapsTo k v rm <-> is_addk_of k v (snd p1) (-(1)) (snd p2)),
      sub_spec p1 p2 (fst p1 + (-(1)) * fst p2, rm).
  Theorem sub_dec : forall p1 p2, sub_spec p1 p2 (sub p1 p2).
  Proof.
    intros p1 p2; unfold sub; destruct (addk_dec p1 (- (1)) p2).
    discriminate.
    constructor; intros; simpl; auto.
  Qed.

  Theorem div_dec : forall c p1, mult_spec (Qinv c) p1 (div c p1).
  Proof.
    intros; unfold div; apply mult_dec.
  Qed.

  (** Alternative properties and specs, in terms of [coef_of] *)
  Ltac find_alter_aux :=
    match goal with
      | H : _ = Some _ |- _ => try apply find_2 in H
      | H : _ = None |- _ => try rewrite <- not_find_in_iff in H
    end.
  Ltac find_alter := repeat find_alter_aux.
  CoInductive mult_spec' (c : Q) (p : poly) : poly -> Prop :=
  | mult_spec'_intro : 
    forall (m : poly)
      (Hmult_coef : fst m === c * fst p)
      (Hmult_poly : forall t, m t === c * p t),
      mult_spec' c p m.
  Property mult_dec' : forall c p, mult_spec' c p (mult c p).
  Proof.
    intros; destruct (mult_dec c p); constructor; auto.
    intro t; unfold coef_of; simpl in *; destruct t as [t|].
    case_eq (rm[t]); case_eq (snd p)[t]; intros; find_alter.
    rewrite Hmult_poly in H0; inversion_clear H0; subst. 
    rewrite (MapsTo_fun H H3); reflexivity.
    rewrite Hmult_poly in H0; inversion_clear H0; subst.
    contradiction H; exists q0; assumption.
    destruct (eq_dec c 0). rewrite H1, Qmult_0_l; reflexivity.
    contradiction H0; exists (c*q).
    rewrite Hmult_poly; exists q; auto; apply find_2; auto.
    rewrite Qmult_0_r; reflexivity.
    exact Hmult_coef.
  Qed.

  CoInductive add_const_spec' (c : Q) (p : poly) : poly -> Prop :=
  | add_const_spec'_intro : 
    forall (rm : poly)
      (Hadd_const_spec_coef : rm None === p None + c)
      (Hadd_const_spec_poly : forall t, rm (Some t) === p (Some t)),
      add_const_spec' c p rm.
  Property add_const_dec' : forall c p, add_const_spec' c p (add_const c p).
  Proof.
    intros; unfold add_const; constructor.
    reflexivity.
    intro; reflexivity.
  Qed.
  CoInductive cancel_spec' (v : vars) (p : poly) : poly -> Prop :=
  | cancel_spec'_intro : 
    forall (rm : poly)
      (Hcancel_spec_coef : rm None === p None)
      (Hcancel_spec_poly : forall t, rm (Some t) === 
        if (v == t)%compare then 0 else p (Some t)),
      cancel_spec' v p rm.
  Property cancel_dec' : forall v p, cancel_spec' v p (cancel v p).
  Proof.
    intros; unfold cancel; constructor.
    reflexivity.
    intro t; simpl; destruct (eq_dec v t).
    rewrite remove_eq_o; auto.
    rewrite remove_neq_o; auto.
  Qed.

  CoInductive addk_spec' (p1 : poly) (k : Q) (p2 : poly) : poly -> Prop :=
  | addk_spec'_intro :
    forall (rm : poly)
      (Haddk_coef : fst rm === fst p1 + k * fst p2)
      (Haddk_poly : forall t, rm (Some t) === p1 (Some t) + k * p2 (Some t)),
      addk_spec' p1 k p2 rm.
  Property addk_dec' : forall p1 k p2, addk_spec' p1 k p2 (addk p1 k p2).
  Proof.
    intros; destruct (addk_dec p1 k p2); constructor; auto.
    rewrite Hknul, Qmult_0_l, Qplus_0_r; reflexivity.
    intro t; rewrite Hknul, Qmult_0_l, Qplus_0_r; reflexivity.
    intros; unfold coef_of; simpl.
    case_eq (rm[t]); intros; find_alter.
    rewrite Haddk_poly in H; inversion_clear H; subst.
    rewrite (find_1 H0), (find_1 H1); red; ring.
    rewrite not_find_in_iff in H1; rewrite (find_1 H0), H1; red; ring.
    rewrite not_find_in_iff in H2; rewrite (find_1 H1), H2; red; ring.
    case_eq (snd p1)[t]; case_eq (snd p2)[t]; intros; find_alter.
    destruct (eq_dec (q0 + k * q) 0); auto.
    contradiction H; exists (q0 + k * q); rewrite Haddk_poly.
    constructor 1 with q0 q; auto.
    contradiction H; exists q; rewrite Haddk_poly.
    constructor 2; auto.
    contradiction H; exists (k * q); rewrite Haddk_poly.
    constructor 3 with q; auto.
    red; ring.
  Qed.
  
  CoInductive add_monome_spec' (t : vars) (c : Q) (p : poly) : poly -> Prop :=
  | add_monome_spec'_intro :
    forall (rm : poly)
      (Hadd_monome_coef : fst rm = fst p)
      (Hadd_monome_poly : forall t', 
        if (t == t')%compare then rm (Some t') === c + p (Some t')
          else rm (Some t') === p (Some t')),
      add_monome_spec' t c p rm.
  Property add_monome_dec' : forall t c p,
    add_monome_spec' t c p (add_monome t c p).
  Proof.
    intros; destruct (add_monome_dec t c p); constructor; auto.
    intro t'; destruct (eq_dec t t'); try rewrite Hcnul, Qplus_0_l; reflexivity.
    intro; destruct (eq_dec t t') as [E|N]; unfold coef_of; simpl.
    case_eq (rm[t']); case_eq (snd p)[t']; intros; find_alter.
    rewrite Hadd_monome_poly in H0; inversion_clear H0; subst.
    rewrite E in H2; rewrite (MapsTo_fun H H2); red; ring.
    order.
    contradiction H3; exists q; assumption.
    rewrite Hadd_monome_poly in H0; inversion_clear H0; subst.
    contradiction H; exists qt; rewrite H1; assumption.
    contradiction H; exists q; assumption.
    red; ring.
    destruct (eq_dec (c + q) 0); auto.
    contradiction H0; exists (q+c*1); rewrite Hadd_monome_poly.
    constructor 1 with q; auto. rewrite E; auto.
    rewrite Qmult_1_r, Qplus_comm; auto.
    contradiction H0; exists (c*1); rewrite Hadd_monome_poly.
    constructor 3; auto.
    case_eq (rm[t']); case_eq (snd p)[t']; intros; find_alter.
    rewrite Hadd_monome_poly in H0; inversion_clear H0; subst.
    order. rewrite (MapsTo_fun H H2); reflexivity. contradiction N; auto.
    rewrite Hadd_monome_poly in H0; inversion_clear H0; subst.
    contradiction N; auto.
    contradiction H; exists q; assumption.
    contradiction N; auto.
    contradiction H0; exists q; rewrite Hadd_monome_poly.
    constructor 2; auto; intro abs; auto.
    reflexivity.
  Qed.
  
  CoInductive add_spec' (p1 p2 : poly) : poly -> Prop :=
  | add_spec'_intro :
    forall (rm : poly)
      (Hadd_coef : fst rm === fst p1 + fst p2)
      (Hadd_poly : forall t, rm (Some t) === p1 (Some t) + p2 (Some t)),
      add_spec' p1 p2 rm.
  Property add_dec' : forall p1 p2, add_spec' p1 p2 (add p1 p2).
  Proof.
    intros; unfold add; destruct (addk_dec' p1 1 p2); constructor.
    rewrite Qmult_1_l in Haddk_coef; assumption.
    intro t; rewrite Haddk_poly, Qmult_1_l; reflexivity.
  Qed.

  CoInductive sub_spec' (p1 p2 : poly) : poly -> Prop :=
  | sub_spec'_intro :
    forall (rm : poly)
      (Hsub_coef : fst rm === fst p1 - fst p2)
      (Hsub_poly : forall t, rm (Some t) === p1 (Some t) - p2 (Some t)),
      sub_spec' p1 p2 rm.
  Property sub_dec' : forall p1 p2, sub_spec' p1 p2 (sub p1 p2).
  Proof.
    intros; unfold sub; destruct (addk_dec' p1 (-(1)) p2); constructor.
    rewrite Haddk_coef; red; ring.
    intro t; rewrite Haddk_poly; red; ring.
  Qed.

  Property div_dec' : forall c p, mult_spec' (Qinv c) p (div c p).
  Proof.
    intros; apply mult_dec'.
  Qed.

  (** Corollary of the above : Morphisms on [equiv] *)
  Global Instance mult_equiv : 
    Proper (_eq ==> equiv ==> equiv) mult.
  Proof.
    intros c c' Hc p p' Hp.
    destruct (mult_dec' c p); destruct (mult_dec' c' p').
    intro t; rewrite Hmult_poly, Hmult_poly0, Hc, Hp; reflexivity.
  Qed.

  Global Instance add_const_equiv : 
    Proper (_eq ==> equiv ==> equiv) add_const.
  Proof.
    intros c c' Hc p p' Hp.
    destruct (add_const_dec' c p); destruct (add_const_dec' c' p').
    intros [t|].
    rewrite Hadd_const_spec_poly, Hp; symmetry; auto.
    rewrite Hadd_const_spec_coef, Hp, Hc; symmetry; auto.
  Qed.
  Global Instance cancel_equiv : 
    Proper (_eq ==> equiv ==> equiv) cancel.
  Proof.
    intros k k' Hk p p' Hp.
    destruct (cancel_dec' k p); destruct (cancel_dec' k' p').
    intros [t|].
    rewrite (Hcancel_spec_poly t), (Hcancel_spec_poly0 t).
    rewrite is_compare_m with k k' t t Eq Eq; auto.
    destruct (eq_dec k' t); auto.
    rewrite Hcancel_spec_coef, Hp; symmetry; auto.
  Qed.

  Global Instance add_monome_equiv :
    Proper (_eq ==> _eq ==> equiv ==> equiv) add_monome.
  Proof.
    intros t t' Ht c c' Hc p p' Hp; rewrite Ht in *.
    destruct (add_monome_dec' t' c p); destruct (add_monome_dec' t' c' p').
    intros [z|]. 
    generalize (Hadd_monome_poly z) (Hadd_monome_poly0 z); 
      intros Hz1 Hz2; destruct (eq_dec t' z);
        rewrite Hz1, Hz2, ?Hc, Hp; reflexivity.
    simpl; rewrite Hadd_monome_coef, Hadd_monome_coef0; exact (Hp None).
  Qed.

  Global Instance add_equiv : Proper (equiv ==> equiv ==> equiv) add.
  Proof.
    intros p1 p1' Hp1 p2 p2' Hp2.
    destruct (add_dec' p1 p2); destruct (add_dec' p1' p2').
    intros [z|].
    rewrite Hadd_poly, Hadd_poly0, Hp1, Hp2; reflexivity.
    simpl; rewrite Hadd_coef, Hadd_coef0, (Hp1 None), (Hp2 None); reflexivity.
  Qed.

  Global Instance sub_equiv : Proper (equiv ==> equiv ==> equiv) sub.
  Proof.
    intros p1 p1' Hp1 p2 p2' Hp2.
    destruct (sub_dec' p1 p2); destruct (sub_dec' p1' p2').
    intros [z|].
    rewrite Hsub_poly, Hsub_poly0, Hp1, Hp2; reflexivity.
    simpl; rewrite Hsub_coef, Hsub_coef0, (Hp1 None), (Hp2 None); reflexivity.
  Qed.

  Global Instance div_equiv : Proper (_eq ==> equiv ==> equiv) div.
  Proof.
    repeat intro; unfold div.
    rewrite H, H0; reflexivity.
  Qed.

  (** [equiv] and [===] are actually the same thing as long as polynoms
     are without zero coefficients, which is an invariant that is preserved
     by all the functions above. 
     *)
  Class Wf (p : poly) := {
    Wf_p : forall v q, MapsTo v q (snd p) -> q =/= 0
  }.

  Instance Wf_P0 : Wf P0 := { Wf_p := fun v q Hv Hq => _ }.
  Proof.
    simpl in Hv; rewrite empty_mapsto_iff in Hv; contradiction.
  Qed.
  Instance Wf_P1 : Wf P1 := { Wf_p := fun v q Hv Hq => _ }.
  Proof.
    simpl in Hv; rewrite empty_mapsto_iff in Hv; contradiction.
  Qed.
  Instance Wf_Pz (z : Z) : Wf (Pz z) := { Wf_p := fun v q Hv Hq => _ }.
  Proof.
    simpl in Hv; rewrite empty_mapsto_iff in Hv; contradiction.
  Qed.
  Instance Wf_Pq (q : Q) : Wf (Pq q) := { Wf_p := fun v q Hv Hq => _ }.
  Proof.
    simpl in Hv; rewrite empty_mapsto_iff in Hv; contradiction.
  Qed.

  Instance Wf_embed (v : vars) : Wf (embed v) := 
    { Wf_p := fun v q Hv Hq => _ }.
  Proof.
    simpl in Hv; rewrite add_mapsto_iff, empty_mapsto_iff in Hv; destruct Hv.
    destruct H; subst; discriminate. destruct H; contradiction.
  Qed.
  Instance Wf_mult (c : Q) `{Wf p} : Wf (mult c p) :=
    { Wf_p := fun v q Hv Hq => _ }.
  Proof.
    destruct (mult_dec c p); simpl in *.
    rewrite Hmult_poly  in Hv; inversion_clear Hv; subst.
    assert (R := Qmult_integral_l _ _ H0 Hq).
    destruct H; exact (Wf_p0 v q0 H2 R).
  Qed.
  Instance Wf_add_const (c : Q) `{Wf p} : Wf (add_const c p) :=
    { Wf_p := fun v q Hv Hq => _ }.
  Proof.
    unfold add_const in Hv; simpl in *.
    apply (Wf_p Hv Hq).
  Qed.
  Instance Wf_cancel (v : vars) `{Wf p} : Wf (cancel v p) :=
    { Wf_p := fun v q Hv Hq => _ }.
  Proof.
    unfold cancel in Hv; simpl in *.
    refine (@Wf_p _ H v q _ Hq); apply remove_3 with v0; auto.
  Qed.
  
  Property Wf_addk_m : 
    forall p1 k p2, 
      k =/= 0 ->
      (forall v q, MapsTo v q p1 -> q =/= 0) ->
      (forall v q, MapsTo v q p2 -> q =/= 0) ->
      forall v q, MapsTo v q (addk_m p1 k p2) -> q =/= 0.
  Proof.
    intros p1 k p2 Hk H1 H2; destruct (addk_m_dec p1 k p2).
    intros v q H; rewrite Haddk_poly in H; inversion_clear H; subst.
    assumption.
    eauto. 
    intro abs; refine (H2 v q2 H3 _).
    exact (Qmult_integral_l _ _ Hk abs).
  Qed.
  Instance Wf_addk `{Wf p1} k `{Wf p2} : Wf (addk p1 k p2).
  Proof.
    intros; unfold addk; simpl.
    destruct (eq_dec k 0); auto.
    constructor; apply Wf_addk_m; auto.
    destruct H; auto.
    destruct H0; auto.
  Qed.
  Instance Wf_add_monome (t : vars) (coef : Q) `{Wf p} : 
    Wf (add_monome t coef p).
  Proof.
    intros; unfold add_monome; simpl.
    destruct (eq_dec coef 0); auto.
    constructor; apply Wf_addk_m.
    intro; auto.
    destruct H; auto.
    destruct (Wf_embed t); auto.
  Qed.

  Instance Wf_add `{Wf p1, Wf p2} : Wf (add p1 p2).
  Proof.
    intros; unfold add; simpl.
    apply Wf_addk; auto.
  Qed.
  Instance Wf_sub `{Wf p1, Wf p2} : Wf (sub p1 p2).
  Proof.
    intros; unfold sub; simpl.
    apply Wf_addk; auto.
  Qed.

  Instance Wf_div (c : Q) `{Wf p} : Wf (div c p).
  Proof.
    intros; unfold div; eauto with typeclass_instances.
  Qed.

  Theorem wf_equiv_iff `{H1 : Wf p1, H2 : Wf p2} :
    equiv p1 p2 <-> p1 === p2.
  Proof.
    intros; split; intro H.
    destruct p1; destruct p2; simpl in *.
    constructor.
    exact (H None).
    intros k v; assert (IH := H (Some k)); simpl in IH; clear H.
    split; intros [z [Hvz Hz]].
    apply find_1 in Hz; rewrite Hz in IH.
    destruct (d0[k]) as [ ]_eqn.
    exists q1; split; [order | apply find_2; auto].
    contradiction (Wf_p (p:=(q,d)) (v:=k) (q:=z)); simpl; apply find_2; auto.
    apply find_1 in Hz; rewrite Hz in IH.
    destruct (d[k]) as [ ]_eqn.
    exists q1; split; [order | apply find_2; auto].
    contradiction (Wf_p (p:=(q0,d0)) (v:=k) (q:=z)); 
    auto; simpl; apply find_2; auto.
    rewrite H; reflexivity.
  Qed.

  (** Extra operations, useful for the theory of arithmetic *)
  Definition is_const (p : poly) : option Q :=
    if is_empty (snd p) then Some (fst p) else None.
  Definition vars_of (p : poly) : list vars :=
    fold (fun k _ acc => k::acc) (snd p) nil.
  Definition leaves (p : poly) : list poly :=
    fold (fun k _ acc => (embed k)::acc) (snd p) nil.

  Definition extract (p : poly) : option vars :=
    if (fst p == 0)%compare then 
      match elements (snd p) with
        | (t, q)::nil => 
          if (q == 1)%compare then Some t else None
        | _ => None
      end
      else None.
  Definition choose (p : Map[vars, Q]) : option (vars * Q) :=
    (fix choose_aux l := 
      match l with
        | nil => None
        | (t, k)::q =>
          if (k == 0)%compare then choose_aux q
            else Some (t, k)
      end) (elements p).

  Definition fold_coefs 
    (A : Type) (f : vars -> Q -> A -> A) (p : poly) (i : A) :=
    fold f (snd p) i.

  (** Extra operations are morphisms for [===] *)
  Global Instance leaves_m : Proper (_eq ==> _eq) leaves.
  Proof.
    repeat intro; unfold leaves.
    inversion_clear H; simpl.
    match goal with
      | |- context f [fold ?F b nil] =>
        cut (_eq (fold F b nil) (fold F d nil))
    end.
    intro L; inversion L; subst.
    reflexivity.
    constructor; auto.
    apply fold_m; auto.
    repeat intro.
    constructor; auto; rewrite H; auto.
  Qed.
  
  Global Instance extract_m : Proper (_eq ==> _eq) extract.
  Proof.
    repeat intro; unfold extract.
    inversion_clear H; simpl.
    rewrite is_compare_m with a c 0 0 Eq Eq; auto.
    destruct (eq_dec c 0); [|constructor].
    assert (R := elements_m H1); inversion_clear R; subst.
    constructor.
    inversion_clear H2.
    inversion H3.
    rewrite is_compare_m with b0 d0 1 1 Eq Eq; auto.
    destruct (eq_dec d0 1); constructor; auto.
    constructor.
  Qed.

  Global Instance choose_m : Proper (_eq ==> _eq) choose.
  Proof.
    repeat intro; unfold choose.
    assert (R := elements_m H).
    revert R; generalize (elements x) (elements y); clear x y H.
    induction l; intros l0; destruct l0; intro H; inversion H; subst.
    constructor.
    destruct H3.
    rewrite is_compare_m with b d 0 0 Eq Eq; auto.
    destruct (eq_dec d 0); auto.
    constructor; constructor; auto.
  Qed.

  Global Instance fold_coefs_m `{OrderedType A} :
    Proper ((_eq ==> _eq ==> _eq ==> _eq) ==> _eq ==> _eq ==> _eq)
    (@fold_coefs A).
  Proof.
    repeat intro; unfold fold_coefs.
    apply fold_m; auto.
    destruct H1; assumption.
  Qed.

  (** Extra operations' specs *)
  CoInductive is_const_spec (p : poly) : option Q -> Prop :=
  | is_const_spec_true : 
    forall (His_const : p === (fst p, [])), is_const_spec p (Some (fst p))
  | is_const_spec_false : 
    forall (His_const : p =/= (fst p, [])), is_const_spec p None.
  Property is_const_dec : forall p, is_const_spec p (is_const p).
  Proof.
    intro; unfold is_const.
    destruct (is_empty_dec (snd p)); constructor.
    destruct p; constructor; auto; simpl in *.
    intros k v; split; intros [z [Hzv Hz]].
    contradiction (Htrue _ _ Hz).
    rewrite empty_mapsto_iff in Hz; contradiction.
    intro abs; apply Hfalse; intros z q Hz.
    inversion abs; subst; clear abs; simpl in *.
    destruct (proj1 (H3 z q)) as [x [xz Hx]]; [exists q; split; auto |].
    rewrite empty_mapsto_iff in Hx; contradiction.
  Qed.
  
  CoInductive extract_spec (p : poly) : option vars -> Prop :=
  | extract_spec_None : 
    forall (Hnotembed : forall t, p =/= embed t), extract_spec p None
  | extract_spec_Some : 
    forall t, p === embed t -> extract_spec p (Some t).
  Property extract_dec : forall p, extract_spec p (extract p).
  Proof.
    destruct p; unfold extract; simpl.
    destruct (eq_dec q 0) as [Hq|Hq]; try constructor.
    remember (elements d) as L.
    destruct L; try constructor.
    intros t abs; assert (abs' : In t d).
    unfold embed in abs; inversion_clear abs.
    rewrite H0; exists 1; apply add_1; auto.
    destruct abs'; apply elements_1 in H; rewrite <- HeqL in H; inversion H.
    destruct p as [t qt]; destruct L; try constructor.
    destruct (eq_dec qt 1); try constructor.
    constructor; auto.
    intros k v; split; intros [z [Hvz Hz']].
    apply elements_1 in Hz'; rewrite <- HeqL in Hz'.
    inversion_clear Hz'; subst; inversion_clear H0; simpl in *; subst.
    exists 1; split. transitivity qt; assumption. apply add_1; auto.
    rewrite MapFacts.add_mapsto_iff in Hz'; destruct Hz'.
    destruct H0; subst; exists qt; split; auto.
    transitivity 1; auto.
    apply elements_2; rewrite <- HeqL; left; constructor; auto.
    contradiction (empty_1 (proj2 H0)).
    intros z abs; unfold embed in abs; inversion abs; subst; clear abs.
    destruct (proj2 (H5 z 1)). exists 1; split; auto; apply add_1; auto.
    destruct H0; apply elements_1 in H1; rewrite <- HeqL in H1.
    inversion H1; subst; [|inversion H4].
    apply H; rewrite H0; destruct H4; simpl in H4; rewrite H4; reflexivity.
    destruct p as [u qu]; intros z abs.
    unfold embed in abs; inversion abs; subst; clear abs.
    assert (Heqc := cardinal_m H4).
    rewrite MapInterface.cardinal_1, <- HeqL in Heqc; simpl in Heqc.
    rewrite (cardinal_2 (m:=[]) (x:=z) (e:=1)) in Heqc.
    rewrite cardinal_1 in Heqc; [discriminate Heqc|].
    apply empty_1. rewrite empty_in_iff; tauto.
    intro; reflexivity.
    repeat intro; unfold embed in H; inversion H; auto.
  Qed.
  Property extract_embed : forall t, extract (embed t) = Some t.
  Proof.
    intro t; unfold embed, extract; vm_compute; reflexivity.
  Qed.

  CoInductive choose_spec (m : Map[vars, Q]) : option (vars * Q) -> Prop :=
  | choose_spec_None :
    forall (Hchoose : forall k v, MapsTo k v m -> v === 0), choose_spec m None
  | choose_spec_Some :
    forall k v, MapsTo k v m -> v =/= 0 -> choose_spec m (Some (k, v)).
  Theorem choose_dec : forall m, choose_spec m (choose m).
  Proof.
    intro m; unfold choose.
    assert (H := @MapFacts.elements_mapsto_iff _ _ _ _ Q m).
    assert (sort := elements_3 m).
    revert H sort; generalize (elements m); intro l; revert m.
    induction l; intros.
    constructor; intros k v Hkv; rewrite H in Hkv; inversion Hkv.
    inversion_clear sort; destruct a as [k v]; destruct (eq_dec v 0).
    case (IHl (remove k m)); auto.
    intros k' v'; rewrite MapFacts.remove_mapsto_iff; split; intros.
    rewrite H in H3; destruct H3; inversion_clear H4; auto.
    contradiction (H3 (symmetry (proj1 H5))).
    split; [| rewrite H; right; auto].
    apply lt_not_eq.
    change (lt_key (k, v) (k', v'));
      apply SortA_InfA_InA with _ eq_key_elt l; try solve [intuition 3].
    apply KeyOrderedType.eqke_Equiv.
    apply KeyOrderedType.ltk_SO.
    intros (w,z)(w',z')(Hw,Hz) (w1,z1)(w1',z1')(Hw1,Hz1); simpl in *.
    unfold lt_key, KeyOrderedType.ltk; simpl; subst; intuition order.
    intro IH; constructor; intros k' v' H'.
    destruct (eq_dec k k'). rewrite H in H'; inversion_clear H'.
    inversion H4; simpl in *; subst; assumption.
    contradiction (lt_not_eq (x:=k) (y:=k')).
    change (lt_key (k, v) (k', v')); 
      apply SortA_InfA_InA with _ eq_key_elt l; try solve [intuition 3].
    apply KeyOrderedType.eqke_Equiv.
    apply KeyOrderedType.ltk_SO.
    intros (w,z)(w',z')(Hw,Hz) (w1,z1)(w1',z1')(Hw1,Hz1); simpl in *.
    unfold lt_key, KeyOrderedType.ltk; simpl; subst; intuition order.
    apply (IH k'); apply remove_2; auto.
    intros k' v' H' Hv'; constructor; auto.
    apply remove_3 with k; auto.
    constructor; auto; rewrite H; constructor; auto.
  Qed.

End WithVars.
End RAW.

Module FULL.
  (** Alternative version of polynoms, with the non-zero-coefficients
     invariants added in a sigma-type. *)
  Section WithVars.
    Variable vars : Set.
    Context `{vars_OT : OrderedType vars}.

    Structure poly := mk_poly {
      _this : @RAW.poly vars _;
      wf_this : RAW.Wf _this
    }.

    (** Constant polynoms 0 and 1, and z for all z *)
    Definition P0 : poly := mk_poly (@RAW.Wf_P0 vars _).
    Definition P1 : poly := mk_poly (@RAW.Wf_P1 vars _).
    Definition Pz (z : Z) : poly := mk_poly (@RAW.Wf_Pz vars _ z).
    Definition Pq (q : Q) : poly := mk_poly (@RAW.Wf_Pq vars _ q).
  
    Definition embed (v : vars) : poly := 
      mk_poly (@RAW.Wf_embed vars _ v).

    (** Constructors *)
    Definition mult (c : Q) (p : poly) : poly :=
      mk_poly (@RAW.Wf_mult vars _ c _ (wf_this p)).
    Definition add_const (c : Q) (p : poly) : poly :=
      mk_poly (@RAW.Wf_add_const vars _ c _ (wf_this p)).
    Definition cancel (v : vars) (p : poly) : poly :=
      mk_poly (@RAW.Wf_cancel vars _ v _ (wf_this p)).
    Definition addk (p1 : poly) (k : Q) (p2 : poly) : poly :=
      mk_poly (@RAW.Wf_addk vars _ _ (wf_this p1) k _ (wf_this p2)).
    Definition add_monome (t : vars) (coef : Q) (p : poly) : poly :=
      mk_poly (@RAW.Wf_add_monome vars _ t coef _ (wf_this p)).
    Definition add (p1 p2 : poly) : poly :=
      mk_poly (@RAW.Wf_add vars _ _ (wf_this p1) _ (wf_this p2)).
    Definition sub (p1 p2 : poly) : poly :=
      mk_poly (@RAW.Wf_sub vars _ _ (wf_this p1) _ (wf_this p2)).
    Definition div (c : Q) (p : poly) : poly :=
      mk_poly (@RAW.Wf_div vars _ c _ (wf_this p)).
    
    (** Access to coefficients and coef-wise equivalence *)
    Definition coef_of (p : poly) (v : option vars) : Q :=
      RAW.coef_of (_this p) v.
    Coercion coef_of : poly >-> Funclass.

    Definition equiv (p1 p2 : poly) := 
      forall t, coef_of p1 t === coef_of p2 t.
    Global Instance coef_of_equiv : 
      Proper (equiv ==> _eq ==> _eq) coef_of.
    Proof.
      repeat intro.
      destruct x; destruct y; unfold coef_of, equiv in *; simpl in *.
      rewrite H0; apply H.
    Qed.
    Global Instance equiv_Equivalence : Equivalence equiv.
    Proof. constructor.
      repeat intro; reflexivity. 
      repeat intro; rewrite H; reflexivity.
      repeat intro; rewrite H, H0; reflexivity. 
    Qed.

    Local Transparent dict MapsTo.

    (** Polynoms as an OrderedType *)
    Definition reminder := RAW.poly_OT.
    Existing Instance reminder.
    Instance poly_SOT : 
      SpecificOrderedType poly equiv := {
        SOT_lt := fun p1 p2 => _this p1 <<< _this p2;
        SOT_cmp := fun p1 p2 => _this p1 =?= _this p2
    }.
    Proof.
      abstract (constructor; repeat intro; simpl in *;
        [order |
          apply (lt_not_eq H);
            destruct x; destruct y; simpl in *;
              rewrite <- RAW.wf_equiv_iff; auto]).
      abstract (
        intros; destruct (compare_dec (_this x) (_this y)); constructor; auto;
          destruct x; destruct y; simpl in *;
            rewrite <- RAW.wf_equiv_iff in H; auto).
    Defined.

    Local Opaque dict MapsTo.

    Global Instance poly_OT : OrderedType poly.
    Proof. 
      apply SOT_as_OT. 
    Defined.

    (** Properties and specs, in terms of [coef_of] *)
    CoInductive embed_spec (t : vars) : poly -> Prop :=
    | embed_spec_intro : 
      forall (m : poly) (Hembed : forall t', m t' === 
        if (t' == Some t)%compare then 1 else 0),
        embed_spec t m.
    Property embed_dec : forall t, embed_spec t (embed t).
    Proof.
      intros; unfold embed; constructor.
      intro t'; unfold coef_of, RAW.embed, RAW.coef_of; simpl.
      destruct (eq_dec t' (Some t)).
      inversion H; subst; inversion H; subst.
      rewrite add_eq_o; auto.
      destruct t'; auto.
      rewrite add_neq_o; auto.
      intro abs; apply H; constructor; auto.
    Qed.
 
    CoInductive mult_spec (c : Q) (p : poly) : poly -> Prop :=
    | mult_spec_intro : 
      forall (m : poly) (Hmult : forall t, m t === c * p t),
        mult_spec c p m.
    Property mult_dec : forall c p, mult_spec c p (mult c p).
    Proof.
      intros; destruct p as [p pwf]; unfold mult; simpl; constructor.
      intros; unfold coef_of; simpl; destruct (RAW.mult_dec' c p); auto.
    Qed.

    CoInductive add_const_spec (c : Q) (p : poly) : poly -> Prop :=
    | add_const_spec_intro : 
      forall (m : poly) 
        (Hadd_const_coef : m None === p None + c)
        (Hadd_const_poly : forall t, m (Some t) === p (Some t)),
        add_const_spec c p m.
    Property add_const_dec : forall c p, add_const_spec c p (add_const c p).
    Proof.
      intros; destruct p as [p pwf]; unfold add_const; simpl; constructor.
      intros; simpl; destruct (RAW.add_const_dec' c p); auto.
      intros; reflexivity.
    Qed.

    CoInductive cancel_spec (v : vars) (p : poly) : poly -> Prop :=
    | cancel_spec_intro : 
      forall (m : poly) 
        (Hcancel_coef : m None === p None)
        (Hcancel_poly : forall t, m (Some t) === 
          if (v == t)%compare then 0 else p (Some t)),
        cancel_spec v p m.
    Property cancel_dec : forall v p, cancel_spec v p (cancel v p).
    Proof.
      unfold cancel; intros; destruct p as [p pwf]; constructor.
      reflexivity.
      intro t; simpl.
      change (RAW.coef_of (RAW.cancel v p) (Some t) === 
        if (v == t)%compare then 0 else (RAW.coef_of p) (Some t)).
      destruct (RAW.cancel_dec' v p); auto.
    Qed.

    CoInductive addk_spec (p1 : poly) (k : Q) (p2 : poly) : poly -> Prop :=
    | addk_spec_intro :
      forall (rm : poly) (Hadd : forall t, rm t === p1 t + k * p2 t),
        addk_spec p1 k p2 rm.
    Property addk_dec : forall p1 k p2, addk_spec p1 k p2 (addk p1 k p2).
    Proof.
      intros; destruct p1 as [p1 p1wf]; destruct p2 as [p2 p2wf]; 
        unfold addk; simpl; constructor.
      intros; unfold coef_of; simpl; destruct (RAW.addk_dec' p1 k p2).
      destruct t; auto.
    Qed.
        
    CoInductive add_monome_spec (t : vars) (c : Q) (p : poly) : poly -> Prop :=
    | add_monome_spec_intro :
      forall (rm : poly)
        (Hadd_monome : forall t', 
          if (Some t == t')%compare then 
            rm t' === c + p t' else rm t' === p t'),
        add_monome_spec t c p rm.
    Property add_monome_dec : forall t c p,
      add_monome_spec t c p (add_monome t c p).
    Proof.
      intros; destruct p as [p pwf]; unfold add_monome; simpl; constructor.
      intros; unfold coef_of; simpl; destruct (RAW.add_monome_dec' t c p).
      destruct t' as [t' |].
      assert (H := Hadd_monome_poly t'); clear Hadd_monome_poly.
      destruct (eq_dec t t'); destruct (eq_dec (Some t) (Some t')); auto.
      contradiction H1; constructor; auto.
      inversion H1; order.
      destruct (eq_dec (Some t) None).
      inversion H.
      simpl; rewrite Hadd_monome_coef; reflexivity.
    Qed.
    
    CoInductive add_spec (p1 p2 : poly) : poly -> Prop :=
    | add_spec_intro :
      forall (rm : poly) (Hadd : forall t, rm t === p1 t + p2 t),
        add_spec p1 p2 rm.
    Property add_dec : forall p1 p2, add_spec p1 p2 (add p1 p2).
    Proof.
      intros; destruct p1 as [p1 p1wf]; destruct p2 as [p2 p2wf]; 
        unfold add; simpl; constructor.
      intros; unfold coef_of; simpl; destruct (RAW.add_dec' p1 p2).
      destruct t; auto.
    Qed.
    CoInductive sub_spec (p1 p2 : poly) : poly -> Prop :=
    | sub_spec_intro :
      forall (rm : poly) (Hsub : forall t, rm t === p1 t - p2 t),
        sub_spec p1 p2 rm.
    Property sub_dec : forall p1 p2, sub_spec p1 p2 (sub p1 p2).
    Proof.
      intros; destruct p1 as [p1 p1wf]; destruct p2 as [p2 p2wf]; 
        unfold sub; simpl; constructor.
      intros; unfold coef_of; simpl; destruct (RAW.sub_dec' p1 p2).
      destruct t; auto.
    Qed.
    
    Property div_dec : forall c p, mult_spec (Qinv c) p (div c p).
    Proof.
      intros; destruct p as [p pwf]; unfold div; simpl; constructor.
      intros; unfold coef_of; simpl; destruct (RAW.div_dec' c p); auto.
    Qed.
    
    (** Corollary of the above : Morphisms on [equiv] *)
    Global Instance mult_equiv : 
      Proper (_eq ==> equiv ==> equiv) mult.
    Proof.
      intros c c' Hc p p' Hp.
      destruct (mult_dec c p); destruct (mult_dec c' p').
      intro t; rewrite (Hmult t), (Hmult0 t), Hc, (Hp t); reflexivity.
    Qed.

    Global Instance add_const_equiv : 
      Proper (_eq ==> equiv ==> equiv) add_const.
    Proof.
      intros c c' Hc p p' Hp.
      destruct (add_const_dec c p); destruct (add_const_dec c' p').
      intros [t|].
      rewrite (Hadd_const_poly t), (Hp (Some t)); 
        symmetry; apply Hadd_const_poly0.
      rewrite Hadd_const_coef, (Hp None), Hc; auto.
    Qed.

    Global Instance cancel_equiv : 
      Proper (_eq ==> equiv ==> equiv) cancel.
    Proof.
      intros k k' Hk p p' Hp.
      destruct (cancel_dec k p); destruct (cancel_dec k' p').
      intros [t|].
      rewrite (Hcancel_poly t), (Hcancel_poly0 t).
      rewrite RAW.is_compare_m with k k' t t Eq Eq; auto.
      destruct (eq_dec k' t); auto.
      rewrite Hcancel_coef, (Hp None); auto.
    Qed.

    Global Instance addk_equiv : 
      Proper (equiv ==> _eq ==> equiv ==> equiv) addk.
    Proof.
      intros p1 p1' Hp1 k k' Hk p2 p2' Hp2.
      destruct (addk_dec p1 k p2); destruct (addk_dec p1' k' p2').
      intro t; rewrite (Hadd t), (Hadd0 t), (Hp1 t), (Hp2 t), Hk; reflexivity.
    Qed.

    Global Instance add_monome_equiv :
      Proper (_eq ==> _eq ==> equiv ==> equiv) add_monome.
    Proof.
      intros t t' Ht c c' Hc p p' Hp.
      destruct (add_monome_dec t c p); destruct (add_monome_dec t' c' p').
      intro z; generalize (Hadd_monome z) (Hadd_monome0 z); intros Hz1 Hz2.
      destruct (eq_dec (Some t) z); destruct (eq_dec (Some t') z).
      rewrite Hz1, Hz2, ?Hc, (Hp z); reflexivity.
      contradiction H0; rewrite <- H; constructor; auto.
      contradiction H; rewrite <- H0; constructor; auto.
      rewrite Hz1, Hz2, ?Hc, (Hp z); reflexivity.
    Qed.
    
    Global Instance add_equiv : 
      Proper (equiv ==> equiv ==> equiv) add.
    Proof.
      intros p1 p1' Hp1 p2 p2' Hp2.
      destruct (add_dec p1 p2); destruct (add_dec p1' p2').
      intro t; rewrite (Hadd t), (Hadd0 t), (Hp1 t), (Hp2 t); reflexivity.
    Qed.
    
    Global Instance sub_equiv : 
      Proper (equiv ==> equiv ==> equiv) sub.
    Proof.
      intros p1 p1' Hp1 p2 p2' Hp2.
      destruct (sub_dec p1 p2); destruct (sub_dec p1' p2').
      intro t; rewrite (Hsub t), (Hsub0 t), (Hp1 t), (Hp2 t); reflexivity.
    Qed.
    
    Global Instance div_equiv : 
      Proper (_eq ==> equiv ==> equiv) div.
    Proof.
      intros c c' Hc p p' Hp.
      destruct (div_dec c p); destruct (div_dec c' p').
      intro t; rewrite (Hmult t), (Hmult0 t), Hc, (Hp t); reflexivity.
    Qed.

    (** Meaning of operations given as rewrite rules through [coef_of] *)
    Remark P0_co : forall t, P0 t === 0.
    Proof.
      intro t; unfold equiv, coef_of, RAW.coef_of; simpl.
      destruct t; auto; rewrite empty_o; reflexivity.
    Qed.
    Remark P1_co : forall t, P1 t === match t with None => 1 | _ => 0 end.
    Proof.
      intro t; unfold equiv, coef_of, RAW.coef_of; simpl.
      destruct t; auto; rewrite empty_o; reflexivity.
    Qed.
    Remark Pz_co : forall z t, Pz z t === match t with None => z#1 | _ => 0 end.
    Proof.
      intro t; unfold equiv, coef_of, RAW.coef_of; simpl.
      destruct t; auto; rewrite empty_o; reflexivity.
    Qed.
    Remark Pq_co : forall q t, Pq q t === match t with None => q | _ => 0 end.
    Proof.
      intro t; unfold equiv, coef_of, RAW.coef_of; simpl.
      destruct t; auto; rewrite empty_o; reflexivity.
    Qed.

    Remark embed_co : forall v t, embed v t === 
      if (t == Some v)%compare then 1 else 0.
    Proof.
      intros; destruct (embed_dec v); auto.
    Qed.   
    Remark mult_co : forall k a t, mult k a t === k * a t.
    Proof.
      intros; destruct (mult_dec k a); auto.
    Qed.
    Remark add_const_co : forall k a t, add_const k a t === 
      match t with None => a None + k | _ => a t end.
    Proof.
      intros; destruct (add_const_dec k a).
      destruct t; auto.
    Qed.
    Remark cancel_co : forall v a t, cancel v a t === 
      if (Some v == t)%compare then 0 else a t.
    Proof.
      intros; destruct (cancel_dec v a).
      destruct t; auto.
      rewrite Hcancel_poly.
      destruct (eq_dec v v0); destruct (eq_dec (Some v) (Some v0)); auto.
      contradiction H0; constructor; auto.
      inversion H0; subst; contradiction H; auto.
    Qed.
    Remark addk_co : forall a k b t, addk a k b t === a t + k * b t.
    Proof.
      intros; destruct (addk_dec a k b); auto.
    Qed.
    Remark add_monome_co : forall v k a t, add_monome v k a t ===
      if (Some v == t)%compare then k + a t else a t.
    Proof.
      intros; destruct (add_monome_dec v k a).
      assert (Ht := Hadd_monome t); clear Hadd_monome.
      destruct (eq_dec (Some v) t); auto.
    Qed.
    Remark add_co : forall a b t, add a b t === a t + b t.
    Proof.
      intros; destruct (add_dec a b); auto.
    Qed.
    Remark sub_co : forall a b t, sub a b t === a t - b t.
    Proof.
      intros; destruct (sub_dec a b); auto.
    Qed.
    Remark div_co : forall k a t, div k a t === / k * a t.
    Proof.
      intros; destruct (div_dec k a); auto.
    Qed.

    (** Extra operations, useful for the theory of arithmetic *)
    Definition is_const (p : poly) : option Q :=
      RAW.is_const (_this p).
    Definition leaves (p : poly) : list poly :=
      fold (fun k _ acc => (embed k)::acc) (snd (_this p)) nil.
    
    Definition extract (p : poly) : option vars :=
      RAW.extract (_this p).
    Definition choose (p : poly) : option (vars * Q) :=
      RAW.choose (snd (_this p)).

    Global Instance is_const_equiv : 
      Proper (equiv ==> _eq) is_const.
    Proof.
      repeat intro; unfold is_const, RAW.is_const.
      destruct x as [x px]; destruct y as [y py]; simpl in *.
      assert (E : RAW.equiv x y) by exact H.
      assert (cut : is_empty (snd x) = is_empty (snd y)).
      destruct (is_empty_dec (snd x)).
      symmetry; rewrite <- is_empty_iff.
      intros z q Hz.
      assert (E' := E (Some z)); unfold RAW.coef_of in E'.
      rewrite (find_1 Hz) in E'; destruct (snd x)[z] as [ ]_eqn:Hxz.
      exact (Htrue z q0 (find_2 Hxz)).
      exact (RAW.Wf_p Hz (symmetry E')).
      destruct (is_empty_dec (snd y)); auto.
      contradiction Hfalse; intros z v Hz.
      assert (E' := E (Some z)); unfold RAW.coef_of in E'.
      rewrite (find_1 Hz) in E'; destruct (snd y)[z] as [ ]_eqn:Hyz.
      contradiction (Htrue _ _ (find_2 Hyz)).
      exact (RAW.Wf_p Hz E').
      rewrite cut; destruct (is_empty (snd y)); constructor.
      exact (H None).
    Qed.

    Global Instance leaves_equiv : Proper (equiv ==> _eq) leaves.
    Proof.
      repeat intro; unfold leaves.
      apply RAW.fold_m; auto.
      repeat intro; constructor; auto.
      assert (He:RAW.embed x0 === RAW.embed y0) by (exact (RAW.embed_m H0)).
      rewrite <- RAW.wf_equiv_iff in He; auto using RAW.Wf_embed.
      destruct x as [x px]; destruct y as [y py]; simpl.
      unfold equiv, coef_of in H; simpl in H.
      change (RAW.equiv x y)  in H; rewrite RAW.wf_equiv_iff in H; auto.
      inversion H; assumption.
    Qed.

    Global Instance extract_equiv : Proper (equiv ==> _eq) extract.
    Proof.
      repeat intro; unfold extract.
      apply RAW.extract_m.
      change (_this x === _this y).
      rewrite <- RAW.wf_equiv_iff; auto using wf_this.
    Qed.
      
    Global Instance choose_equiv : Proper (equiv ==> _eq) choose.
    Proof.
      repeat intro; unfold choose.
      apply RAW.choose_m.
      cut (_this x === _this y).
      intro Z; inversion Z; auto.
      rewrite <- RAW.wf_equiv_iff; auto using wf_this.
    Qed.

    CoInductive is_const_spec (p : poly) : option Q -> Prop :=
    | is_const_spec_true : 
      forall c (His_const : p === add_const c P0), is_const_spec p (Some c)
    | is_const_spec_false : 
      forall (His_const : p =/= add_const (p None) P0), is_const_spec p None.
    Property is_const_dec : forall p, is_const_spec p (is_const p).
    Proof.
      intros [p pwf]; unfold is_const; simpl; 
        destruct (RAW.is_const_dec p); constructor.
      intro t; unfold coef_of; simpl.
      rewrite <- RAW.wf_equiv_iff in His_const; auto.
      rewrite (His_const t); unfold RAW.coef_of; simpl.
      destruct (RAW.add_const_dec' (fst p) (@RAW.P0 _ _)).
      destruct t; auto; red; ring.
      constructor; intros; simpl in *.
      rewrite empty_mapsto_iff in H; contradiction.
      intro abs; apply His_const.
      rewrite <- RAW.wf_equiv_iff; auto.
      intro z; destruct z; simpl; auto.
      assert (Hv := abs (Some v)).
      simpl in Hv. assumption.
      constructor; intros.
      contradiction (empty_1 H).
    Qed.

    Property leaves_iff : 
      forall p t, InA equiv (embed t) (leaves p) <-> p (Some t) =/= 0.
    Proof.
      intros [p pwf] t; unfold leaves; simpl.
      destruct p as [c m]; simpl.
      apply fold_rec_bis with (P := fun mvu L => InA equiv (embed t) L <->
        match mvu[t] with Some q => q | None => 0 end =/= 0); intros.
      rewrite H in H0; exact H0.
      rewrite empty_o; split; intro abs.
      inversion abs. contradiction abs; auto.
      assert (He := RAW.Wf_p (p:=(c,m)) H).
      rewrite add_o; split; intro Z.
      inversion Z; subst; clear Z.
      destruct (eq_dec k t); auto.
      assert (abs := H3 (Some k)); rewrite 2embed_co in abs.
      destruct (eq_dec (Some k) (Some t)).
      inversion H4; subst; contradiction H2; auto.
      unfold is_compare in abs;      
        rewrite (elim_compare_eq (reflexivity (Some k))) in abs.
      discriminate abs.
      rewrite H1 in H3.
      destruct (eq_dec k t); auto.
      destruct (eq_dec k t); auto.
      constructor 1.
      intro z; rewrite 2embed_co.
      rewrite RAW.is_compare_m with z z (Some t) (Some k) Eq Eq; auto.
      constructor; auto.
      constructor 2; rewrite H1; exact Z.
    Qed.
  
    CoInductive extract_spec (p : poly) : option vars -> Prop :=
    | extract_spec_None :
      forall (Hnotembed : forall t, p =/= embed t), extract_spec p None
    | extract_spec_Some : 
      forall t, p === embed t -> extract_spec p (Some t).
    Property extract_dec : forall p, extract_spec p (extract p).
    Proof.
      destruct p as [p pwf]; unfold extract; simpl.
      destruct (RAW.extract_dec p); constructor.
      intros t abs; apply (Hnotembed t).
      rewrite <- RAW.wf_equiv_iff; auto using RAW.Wf_embed.
      rewrite <- RAW.wf_equiv_iff in H; auto using RAW.Wf_embed.
    Qed.
    Property extract_embed : forall t, extract (embed t) = Some t.
    Proof.
      intro t; unfold embed, extract; vm_compute; reflexivity.
    Qed.

    CoInductive choose_spec (p : poly) : option (vars * Q) -> Prop :=
    | choose_spec_None :
      forall (Hchoose : p === add_const (p None) P0), choose_spec p None
    | choose_spec_Some :
      forall k v, p (Some k) = v -> v =/= 0 -> choose_spec p (Some (k, v)).
    Theorem choose_dec : forall m, choose_spec m (choose m).
    Proof.
      intros [p pwf]; unfold choose; simpl; destruct (RAW.choose_dec (snd p)).
      constructor.
      intro t; unfold coef_of, RAW.coef_of; destruct p; simpl.
      destruct t; [ | red; ring].
      rewrite empty_o; destruct d[v] as [ ]_eqn; auto.
      exact (Hchoose _ _ (find_2 Heqo)).
      constructor; auto.
      unfold coef_of, RAW.coef_of; simpl.
      rewrite (find_1 H); reflexivity.
    Qed.
  End WithVars.
  Global Opaque coef_of.
End FULL.
