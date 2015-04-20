Require Import Containers.Sets.
Require Containers.SetEqProperties. Module EProps := SetEqProperties.
Require Containers.SetProperties. Module Props := SetProperties.
Require Import SetoidList.
(* Require Import FMapFacts. *)

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.
Open Scope set_scope.

(* Parameter fold_ind :  *)
(*   forall (A : Type) (P : K.t -> A -> Type)  *)
(*     (f : E.t -> A -> A) (i : A) (s : K.t), *)
(*     (forall (s s' : K.t) (a : A), K.eq s s' -> P s a -> P s' a) -> *)
(*     P K.empty i ->  *)
(*     (forall e a s',  *)
(*       K.In e s -> ~K.In e s' -> P s' a -> P (K.add e s') (f e a)) -> *)
(*     P s (K.fold f s i). *)
  
(* Parameter fold_ind2 : *)
(*   forall (A : Type) (P : A -> Type) (f : E.t -> A -> A) (i : A) (s : K.t), *)
(*     P i -> (forall e a, K.In e s -> P a -> P (f e a)) -> *)
(*     P (K.fold f s i). *)

(* Parameter fold_rel :  *)
(*   forall (Acc1 Acc2 : Type) (R : Acc1 -> Acc2 -> Type) *)
(*     (f1 : E.t -> Acc1 -> Acc1) (f2 : E.t -> Acc2 -> Acc2) *)
(*     (i1 : Acc1) (i2 : Acc2) (s : K.t), *)
(*     R i1 i2 -> *)
(*     (forall (k : K.elt) (a1 : Acc1) (a2 : Acc2), *)
(*       K.In k s -> R a1 a2 -> R (f1 k a1) (f2 k a2)) -> *)
(*     R (K.fold f1 s i1) (K.fold f2 s i2). *)

(* Module Type MapFoldInterface (E : DecidableType) (M : FMapInterface.WSfun E). *)
(*   Parameter fold_ind :  *)
(*     forall (A Acc : Type) (P : M.t A -> Acc -> Type) *)
(*       (f : E.t -> A -> Acc -> Acc) (i : Acc) (s : M.t A), *)
(*       (forall (s s' : M.t A) (a : Acc), M.Equal s s' -> P s a -> P s' a) -> *)
(*       P (M.empty A) i -> *)
(*       (forall (k : M.key) (e : A) (a : Acc) (s' : M.t A), *)
(*         M.MapsTo k e s -> ~M.In k s' -> P s' a -> P (M.add k e s') (f k e a))-> *)
(*       P s (M.fold f s i). *)

(*   Parameter fold_ind2 : *)
(*     forall (A Acc : Type) (P : Acc -> Type)  *)
(*       (f : E.t -> A -> Acc -> Acc) (i : Acc) (s : M.t A), *)
(*       P i -> (forall k e a, M.MapsTo k e s -> P a -> P (f k e a)) -> *)
(*       P (M.fold f s i). *)

(*   Parameter fold_rel : *)
(*     forall (A Acc1 Acc2 : Type) (R : Acc1 -> Acc2 -> Type) *)
(*       (f1 : E.t -> A -> Acc1 -> Acc1) (f2 : E.t -> A -> Acc2 -> Acc2) *)
(*       (i1 : Acc1) (i2 : Acc2) (s : M.t A), *)
(*       R i1 i2 -> *)
(*       (forall (k : M.key) (e : A) (a1 : Acc1) (a2 : Acc2), *)
(*         M.MapsTo k e s -> R a1 a2 -> R (f1 k e a1) (f2 k e a2)) -> *)
(*       R (M.fold f1 s i1) (M.fold f2 s i2). *)
(* End MapFoldInterface. *)

Section Reverse_Induction.
  Variable A : Type.
  
  Lemma rev_list_rec :
    forall P:list A-> Type,
      P nil ->
      (forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
      forall l:list A, P (rev l).
  Proof.
    induction l; auto.
  Qed.
  
  Theorem rev_rec :
    forall P:list A -> Type,
      P nil ->
      (forall (x:A) (l:list A), P l -> P (app l (x :: nil))) ->
      forall l:list A, P l.
  Proof.
    intros.
    generalize (rev_involutive l).
    intros E; rewrite <- E.
    apply rev_list_rec.
    auto.
    simpl in |- *.
    intros.
    apply (X0 a (rev l0)).
    auto.
  Qed.
End Reverse_Induction.

Module SetFoldInd.
  Import SetInterface.
  Section fold_induction.
    Context `{FSetSpecs : @SetInterface.FSetSpecs elt elt_OT F}.
    Variable A : Type.
    Variable P : set elt -> A -> Type.

    Variable f : elt -> A -> A.
    Variable i : A.
    Variable s : set elt.
    
    Hypothesis P_m : forall s s' a, s [=] s' -> P s a -> P s' a.
    Hypothesis Hi : P {} i.
    Hypothesis Hstep : forall e a s',
      e \In s -> ~e \In s' -> P s' a -> P {e; s'} (f e a).

    Definition Pl (l : list elt) (a : A) :=
      forall s, equivlistA _eq (elements s) l -> P s a.
    Lemma Hli : Pl nil i.
    Proof.
      intros s' Hs'.
      assert (Hemp : Empty s'). intros e He.
      rewrite elements_iff in He.
      rewrite (Hs' e) in He; inversion He.
      assert (Hemp' := Props.empty_is_empty_1 Hemp).
      exact (P_m (symmetry Hemp') Hi).
    Qed.

    Fixpoint set_of_list (l : list elt) : set elt :=
      match l with
        | nil => {}
        | a::q => {a; set_of_list q}
      end.
    Remark sofl_1 :
      forall l, equivlistA _eq (elements (set_of_list l)) l.
    Proof.
      induction l; simpl; intro e.
      rewrite Props.elements_empty; reflexivity.
      rewrite <- elements_iff; rewrite add_iff; rewrite elements_iff.
      split; intro H.
      destruct H; [constructor | constructor 2; rewrite <- (IHl e)]; auto.
      inversion H; [left | right]; auto.
      rewrite (IHl e); auto.
    Qed.

    Lemma fold_ind_aux : Pl (elements s) (fold f s i).
    Proof.
      rewrite fold_1.
      assert (forall e, InA _eq e (elements s) -> e \In s).
      intros; auto with set.
      assert (H2 := elements_3w s).
      revert H2 H; pattern (elements s); apply rev_rec.
      intros; simpl; exact Hli.
      intros x L IH IHdup IHin; rewrite fold_left_app; simpl.
      intros s' Hs'.
      cut ({x; set_of_list L} [=] s'); [intro Heq |].
      assert (NoDupA _eq (x::(app L nil))).
      refine (NoDupA_swap _ IHdup); intuition.
      refine (P_m Heq _); apply Hstep.
      apply IHin; rewrite InA_app_iff; intuition.
      rewrite elements_iff.
      rewrite (sofl_1 L x); inversion H; rewrite <- app_nil_end in H2; auto.
      apply IH.
      inversion H; rewrite <- app_nil_end in H3; auto.
      intros e He; apply IHin.
      rewrite InA_alt in He |- *; destruct He as [y [Hy1 Hy2]].
      exists y; intuition.
      apply sofl_1.
      (** - cut : (K.add x (set_of_list L)) [=] s' *)
      intro l; rewrite add_iff; split; intro Hl.
      apply elements_2; rewrite (Hs' l); destruct Hl.
      rewrite InA_alt; exists x; intuition.
      assert (X:= (proj1 (sofl_1 L l)) (elements_1 H)).
      rewrite InA_alt in X |- *; destruct X; exists x0; intuition.
      rewrite elements_iff in Hl; rewrite (Hs' l) in Hl.
      destruct (InA_app Hl); [right | left].
      apply elements_2; rewrite (sofl_1 L l); auto.
      inversion H; try inversion H1; intuition.
    Qed.
  
    Theorem fold_ind : P s (fold f s i).
    Proof.
      apply fold_ind_aux.
      induction (elements s); constructor; intuition.
    Qed.
  End fold_induction.
  Corollary fold_ind2 `{FSetSpecs : @SetInterface.FSetSpecs elt elt_OT F} :
    forall (A : Type) (P : A -> Type) (f : elt -> A -> A) (i : A) (s : set elt),
      P i -> (forall e a, e \In s -> P a -> P (f e a)) ->
      P (fold f s i).
  Proof.
    refine (fun A P f i s Hi Hstep => 
      @fold_ind elt elt_OT F FSetSpecs A (fun _ => P) f i s _ Hi _).
    trivial.
    exact (fun e a _ H _ Ha => Hstep e a H Ha).
  Qed.

  Section fold_relation.
    Context `{FSetSpecs : @SetInterface.FSetSpecs elt elt_OT F}.
    Variables A Acc1 Acc2 : Type.
    Variable R : Acc1 -> Acc2 -> Type.

    Variable f1 : elt -> Acc1 -> Acc1.
    Variable f2 : elt -> Acc2 -> Acc2.
    Variable i1 : Acc1.
    Variable i2 : Acc2.
    Variable s : set elt.
    
    Hypothesis Hi : R i1 i2.
    Hypothesis Hstep : forall k a1 a2, 
      k \In s -> R a1 a2 -> R (f1 k a1) (f2 k a2).
    
    Lemma fold_rel : R (fold f1 s i1) (fold f2 s i2).
    Proof.
      assert (Hin : forall k, InA _eq k (elements s) -> k \In s).
      intros; apply elements_2; auto.
      revert Hin; do 2 rewrite fold_1; pattern (elements s).
      apply rev_rec; simpl; auto.
      intros k L IH Hin; do 2 rewrite fold_left_app; simpl; apply Hstep.
      apply Hin; rewrite <- InA_rev; auto; rewrite rev_unit; constructor.
      reflexivity.
      apply IH; intros k0 Hk0; apply Hin.
      rewrite InA_alt in Hk0 |- *; destruct Hk0 as [y [Hy1 Hy2]].
      exists y; intuition.
    Qed.
  End fold_relation.

End SetFoldInd.

(* Module MapFoldInd (E : DecidableType) (M : FMapInterface.WSfun E) *)
(*   : MapFoldInterface(E)(M). *)

(*   Module Import P := FMapFacts.WProperties_fun(E)(M). *)

(*   Section fold_induction. *)
(*     Variables A Acc : Type. *)
(*     Variable P : M.t A -> Acc -> Type. *)
    
(*     Variable f : E.t -> A -> Acc -> Acc. *)
(*     Variable i : Acc. *)
(*     Variable s : M.t A. *)
    
(*     Let eqke := (@M.eq_key_elt A). *)
(*     Hypothesis P_m :  *)
(*       forall s s' a, M.Equal s s' -> P s a -> P s' a. *)
(*     Hypothesis Hi : P (M.empty A) i. *)
(*     Hypothesis Hstep : forall k e a s', *)
(*       M.MapsTo k e s -> ~M.In k s' -> P s' a ->  *)
(*       P (M.add k e s') (f k e a). *)
    
(*     Definition cPl (l : list (E.t * A)) (a : Acc) := *)
(*       forall s, equivlistA eqke (M.elements s) l -> P s a. *)
(*     Lemma cHli : cPl nil i. *)
(*     Proof. *)
(*       intros s' Hs'. *)
(*       assert (Hemp : M.Empty s'). intros k e He. *)
(*       rewrite F.elements_mapsto_iff in He. *)
(*       unfold eqke in Hs'; rewrite (Hs' (k,e)) in He; inversion He. *)
(*       refine (P_m _ Hi); intro k; transitivity (@None A); [|symmetry]. *)
(*       rewrite <- F.not_find_in_iff; rewrite F.empty_in_iff; intuition. *)
(*       rewrite <- F.not_find_in_iff; intros [e He]. *)
(*       contradiction (Hemp k e He). *)
(*     Qed. *)
    
(*     Fixpoint cmap_of_list (l : list (E.t * A)) : M.t A := *)
(*       match l with *)
(*         | nil => M.empty A *)
(*         | (k,e)::q => M.add k e (cmap_of_list q) *)
(*       end. *)
    
(*     Lemma cmofl_1 : *)
(*       forall l, NoDupA (@M.eq_key A) l ->  *)
(*         equivlistA eqke (M.elements (cmap_of_list l)) l. *)
(*     Proof. *)
(*       induction l; simpl; intros Hnodup [k e]. *)
(*       rewrite elements_empty; reflexivity. *)
(*       destruct a as [ka ea]; unfold eqke; rewrite <- F.elements_mapsto_iff. *)
(*       rewrite F.add_mapsto_iff; rewrite F.elements_mapsto_iff. *)
(*       cut ({E.eq ka k} + {~E.eq ka k}); [intros [E|N] |]. *)
(*       inversion Hnodup; subst; intuition. *)
(*       constructor 1; split; auto. *)
(*       left; split; auto; inversion H0; subst. *)
(*       exact (sym_eq (proj2 H4)). *)
(*       elim H1; rewrite InA_alt in H4 |- *;  *)
(*         destruct H4 as [[k' e'] [[H' _] H'']]; simpl in *. *)
(*       exists (k',e'); split; unfold M.eq_key; simpl; try rewrite E; auto. *)
(*       inversion Hnodup; subst; intuition. *)
(*       constructor 2; fold eqke; rewrite <- (H (k,e)); exact H4. *)
(*       right; split; auto; inversion H0; subst. *)
(*       elim N; exact (E.eq_sym (proj1 H4)). *)
(*       unfold eqke in H; rewrite (H (k,e)); assumption. *)
(*       destruct (E.eq_dec ka k); intuition. *)
(*     Qed. *)

(*     Lemma cfold_ind_aux : cPl (M.elements s) (M.fold f s i). *)
(*     Proof. *)
(*       rewrite M.fold_1. *)
(*       assert (forall k e, InA eqke (k,e) (M.elements s) ->  *)
(*         M.MapsTo k e s). *)
(*       intros; unfold eqke in H;  *)
(*         rewrite <- F.elements_mapsto_iff in H; exact H. *)
(*       assert (H2 := M.elements_3w s). *)
(*       revert H2 H; pattern (M.elements s); apply rev_rec. *)
(*       intros; simpl; exact cHli. *)
(*       intros x L IH IHdup IHin; rewrite fold_left_app; simpl. *)
(*       intros s' Hs'. *)
(*       cut (M.Equal  *)
(*         (M.add (fst x) (snd x) (cmap_of_list L)) s'); [intro Heq |]. *)
(*       assert (NoDupA (@M.eq_key _) (x::L++nil)). *)
(*       refine (NoDupA_swap _ IHdup); unfold M.eq_key in *; intuition. *)
(*       refine (P_m Heq _); apply Hstep. *)
(*       apply IHin; rewrite <- InA_rev; rewrite rev_unit; constructor. *)
(*       unfold eqke; destruct x; simpl; split; intuition. *)
(*       rewrite F.elements_in_iff; fold eqke; intros [e He]. *)
(*       inversion H; rewrite <- app_nil_end in *. *)
(*       rewrite (cmofl_1 H3 (fst x, e)) in He; apply H2. *)
(*       rewrite InA_alt in He |- *;  *)
(*         destruct He as [y [[Hy _] HL]]; exists y; intuition. *)
(*       apply IH. *)
(*       inversion H; rewrite <- app_nil_end in H3; auto. *)
(*       intros k e He; apply IHin. *)
(*       rewrite InA_alt in He |- *; destruct He as [y [Hy1 Hy2]]. *)
(*       exists y; intuition. *)
(*       apply cmofl_1.  *)
(*       inversion H; rewrite <- app_nil_end in H3; auto. *)
(*       (** - cut : (KSet.add x (set_of_list L)) [=] s' *) *)
(*       assert (dup : NoDupA (@M.eq_key A) (x :: rev L)). *)
(*       rewrite <- rev_unit; apply NoDupA_rev;  *)
(*         intros; unfold M.eq_key; intuition. transitivity (fst y); auto. *)
(*       assert (dup' : NoDupA (@M.eq_key A) L). *)
(*       inversion dup; rewrite <- rev_involutive; apply NoDupA_rev;  *)
(*         intros; unfold M.eq_key; intuition. transitivity (fst y); auto. *)
(*       intro l; case_eq (M.find l s'); [intros el Hl2 | intro Hl2]. *)
(*       apply M.find_1; assert (Hl2' := M.find_2 Hl2). *)
(*       rewrite F.add_mapsto_iff; rewrite F.elements_mapsto_iff. *)
(*       rewrite F.elements_mapsto_iff in Hl2'; fold eqke in Hl2'. *)
(*       rewrite (Hs' (l,el)) in Hl2'; destruct (InA_app Hl2'). *)
(*       right; split; [intro Heq |]. *)
(*       inversion dup as [|x0 L0 Hnotx dup2]; subst; apply Hnotx. *)
(*       rewrite InA_rev; rewrite InA_alt in H |- *. *)
(*       destruct H as [y [[Hy1 _] Hy2]]; exists y; intuition.  *)
(*       unfold M.eq_key; transitivity l; intuition. *)
(*       fold eqke; rewrite (cmofl_1 dup' (l,el)); assumption. *)
(*       left; inversion H; subst. destruct H1; intuition. inversion H1. *)
(*       rewrite <- F.not_find_in_iff in Hl2 |- *; intro Hl1; apply Hl2. *)
(*       rewrite F.add_in_iff in Hl1; rewrite F.elements_in_iff in Hl1 |- *. *)
(*       destruct Hl1 as [Heq |[el H1]]. *)
(*       exists (snd x); fold eqke; rewrite (Hs' (l, snd x)). *)
(*       rewrite <- InA_rev; rewrite rev_unit; constructor; split; intuition. *)
(*       exists el; fold eqke; rewrite (Hs' (l,el)). *)
(*       rewrite <- InA_rev; rewrite rev_unit; constructor 2; rewrite InA_rev. *)
(*       fold eqke in H1; exact ((proj1 (cmofl_1 dup' (l,el))) H1). *)
(*     Qed. *)
  
(*     Theorem fold_ind : P s (M.fold f s i). *)
(*     Proof. *)
(*       apply cfold_ind_aux. *)
(*       induction (M.elements s); constructor; intuition. *)
(*     Qed. *)
(*   End fold_induction. *)
(*   Corollary fold_ind2 : *)
(*   forall (A Acc : Type) (P : Acc -> Type)  *)
(*     (f : E.t -> A -> Acc -> Acc) (i : Acc) (s : M.t A), *)
(*     P i -> (forall k e a, M.MapsTo k e s -> P a -> P (f k e a)) -> *)
(*     P (M.fold f s i). *)
(*   Proof. *)
(*     refine (fun A Acc P f i s Hi Hstep =>  *)
(*       @fold_ind A Acc (fun _ => P) f i s _ Hi _). *)
(*     trivial. *)
(*     exact (fun k e a _ H _ Ha => Hstep k e a H Ha). *)
(*   Qed. *)

(*   Section fold_relation. *)
(*     Variables A Acc1 Acc2 : Type. *)
(*     Variable R : Acc1 -> Acc2 -> Type. *)

(*     Variable f1 : E.t -> A -> Acc1 -> Acc1. *)
(*     Variable f2 : E.t -> A -> Acc2 -> Acc2. *)
(*     Variable i1 : Acc1. *)
(*     Variable i2 : Acc2. *)
(*     Variable s : M.t A. *)
      
(*     Let eqke := (@M.eq_key_elt A). *)
(*     Hypothesis Hi : R i1 i2. *)
(*     Hypothesis Hstep : forall k e a1 a2,  *)
(*       M.MapsTo k e s -> R a1 a2 -> R (f1 k e a1) (f2 k e a2). *)
    
(*     Lemma fold_rel : R (M.fold f1 s i1) (M.fold f2 s i2). *)
(*     Proof. *)
(*       assert (Hin : *)
(*         forall k e, InA eqke (k,e) (M.elements s) -> M.MapsTo k e s). *)
(*       intros; unfold eqke in H; rewrite <- F.elements_mapsto_iff in H; auto. *)
(*       revert Hin; do 2 rewrite M.fold_1; pattern (M.elements s). *)
(*       apply rev_rec; simpl; auto. *)
(*       intros [k e] L IH Hin; do 2 rewrite fold_left_app; simpl; apply Hstep. *)
(*       apply Hin; rewrite <- InA_rev; rewrite rev_unit; constructor. *)
(*       split; reflexivity. *)
(*       apply IH; intros k0 e0 Hke0; apply Hin. *)
(*       rewrite InA_alt in Hke0 |- *; destruct Hke0 as [y [Hy1 Hy2]]. *)
(*       exists y; intuition. *)
(*     Qed. *)
(*   End fold_relation. *)

(* End MapFoldInd. *)
