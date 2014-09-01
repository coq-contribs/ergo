Require Import Theory Containers.OrderedTypeEx TermUtils.
Require Import CPolynoms. Import FULL.

(** The type of semantic values for arithmetic : 
   a polynom whose variables are terms. *)
SubClass R := poly (vars := term).

(** Constant polynoms 0 and 1, and z for all z *)
Definition R0 : R := @P0 _ _.
Definition R1 : R := @P1 _ _.
Definition Rz (z : Z) : R := Pz z.

(** The [make] function recursively builds a polynom by
   analyzing the head symbol of its argument :
   -- if it is an uninterpreted symbol, the whole term is added to the map
   -- if it is a constant...
   *)
Fixpoint mk_term (coef : Q) (p : R) (t : term) : R :=
  match t with
    | Term.app (Unint _ _) _ => 
      add_monome t coef p
    | Term.app (Cst DomainZ z) nil => 
      add_const (coef * (z#1)) p
    | Term.app (Op DomainZ Plus) (cons t1 (cons t2 nil)) => 
      mk_term coef (mk_term coef p t1) t2
    | Term.app (Op DomainZ Mult) (cons t1 (cons t2 nil)) => 
      let p1 := mk_term 1%Q R0 t1 in
      let p2 := mk_term 1%Q R0 t2 in
        match is_const p1, is_const p2 with
          | Some c1, Some c2 =>
            add_const (coef * (c1 * c2)) p
          | Some c1, None =>
            addk p  (c1*coef) p2
          | None, Some c2 =>
            addk p (c2*coef) p1
          | None, None =>
            add_monome t coef p
        end
    | Term.app (Op DomainZ Minus) (cons t1 (cons t2 nil)) => 
      mk_term (Qopp coef) (mk_term coef p t1) t2
    | Term.app (Op DomainZ Opp) (cons t1 nil) =>
      mk_term (Qopp coef) p t1
    | _ => add_monome t coef p          
  end.

Definition make (t : term) : R := mk_term 1 R0 t.
Definition one : R := Pq (1#7).

Definition leaves (p : R) :=
  match leaves p with
    | nil => one::nil
    | l => l
  end.

Definition subst (p : R) (P r : R) : R :=
  match extract p with
    | Some t => addk (cancel t r) (r (Some t)) P
    | None => r
  end.

Definition solve (t u : R) : Solution R := 
  let diff := sub t u in
    match choose diff with
      | None =>
        if (diff None == 0)%compare then Solved _ else Unsolvable _
      | Some (t, k) =>
        let P := mult (Qinv (Qopp k)) (cancel t diff) in
          Subst (embed t) P
    end.

Definition R_OT : OrderedType R := @poly_OT term _.
Existing Instance R_OT.

Instance Arith_theory : Theory := {
  R := R;
  R_OT := R_OT;
  make := make;
  one := one;
  leaves := leaves;
  subst := subst;
  solve := solve
}.

Section Test.
  Local Notation f_idx1 := Quote.End_idx.
  Local Notation f_idx2 := (Quote.Left_idx Quote.End_idx).
  Local Notation g_idx1 := (Quote.Right_idx Quote.End_idx).
  Local Notation g_idx2 := (Quote.Left_idx (Quote.Left_idx Quote.End_idx)).
  Local Notation Z_idx := (Quote.Right_idx Quote.End_idx).
  Local Notation r1 := Quote.End_idx.
  Local Notation r2 := (Quote.Left_idx Quote.End_idx).
  Local Notation t := (Term.app (Unint f_idx1 f_idx2) Term.tnil).
  Local Notation u := (Term.app (Unint g_idx1 g_idx2) Term.tnil).
  Local Notation t1 := (Term.app (Cst DomainZ 1%Z) Term.tnil).
  Local Notation t0 := (Term.app (Cst DomainZ 0%Z) Term.tnil).
  Local Notation tr1 := (Term.app (Unint Z_idx r1) Term.tnil).
  Local Notation tr2 := (Term.app (Unint Z_idx r2) Term.tnil).
  
  Definition pl t1 t2 := 
    (Term.app (Op DomainZ Plus) (Term.tcons t1 (Term.tcons t2 Term.tnil))).
  Definition mi t1 t2 := 
    (Term.app (Op DomainZ Minus) (Term.tcons t1 (Term.tcons t2 Term.tnil))).

  Definition stripR (r : R) := 
    let 'mk_poly z _ := r in
      (fst z, MapInterface.elements (snd z)).
  Eval vm_compute in stripR (make t).
  Eval vm_compute in stripR (make u).
  Eval vm_compute in (make t) =?= (make u).
  Eval vm_compute in stripR (make t1).
  Eval vm_compute in stripR (make t0).
  Eval vm_compute in stripR (make tr1).
  Eval vm_compute in stripR (make tr2).
  Eval vm_compute in stripR (make (pl tr1 tr2)).
  Eval vm_compute in stripR (make (pl t0 tr2)).
  Eval vm_compute in stripR (make (pl t0 t1)).
  Eval vm_compute in stripR (make (pl t1 tr1)).
  Eval vm_compute in stripR (make (pl tr1 tr1)).
  Eval vm_compute in stripR (make (mi tr1 tr1)).
End Test.

(** Morphisms *)
Local Instance leaves_m : Proper (_eq ==> _eq) leaves.
Proof.
  repeat intro; unfold leaves.
  assert (Heq := leaves_equiv H).
  inversion Heq; constructor; auto; constructor.
Qed.

Local Instance subst_m : Proper (_eq ==> _eq ==> _eq ==> _eq) subst.
Proof.
  intros p p' Hp P P' HP r r' Hr; unfold subst.
  assert (Rp := extract_equiv Hp).
  inversion_clear Rp; auto.
  rewrite H, HP.
  assert (Hr' := Hr (Some a')).
  rewrite Hr'. rewrite Hr.
  reflexivity.
Qed.

Local Instance solve_m : Proper (_eq ==> _eq ==> solution_eq) solve.
Proof.
  intros t1 t2 Ht u1 u2 Hu; unfold solve.
  assert (Hsub := sub_equiv Ht Hu).
  assert (Heq := choose_equiv Hsub).
  inversion Heq.
  assert (Hnone := Hsub None).
  rewrite RAW.is_compare_m with 
    (sub t1 u1 None) (sub t2 u2 None) 0 0 Eq Eq; auto; reflexivity.
  inversion H1; constructor.
  rewrite H2; reflexivity.
  rewrite Hsub, H3, H2; reflexivity.
Qed.

Opaque R_OT.
(** Properties and specs *)
Theorem leaves_not_empty : forall r, leaves r <> nil.
Proof.
  intros r; unfold leaves.
  destruct (FULL.leaves r); congruence.
Qed.

(* (** Semantic interpretation of semantic values *) *)
(* Section RModels. *)
(*   Definition Rmodel := term -> Q. *)
(*   Global Notation "'sum' RM" := (fun k v acc => RM k * v + acc)(at level 0). *)
(*   Definition Rmodel_of (RM : Rmodel) (r : R) : Q := *)
(*     fold (sum RM) (snd r) (fst r). *)
(*   Global Notation " a < b > " := (Rmodel_of a b)(at level 15, b at next level). *)

(*   Definition Rmodels_eq (RM : Rmodel) (r1 r2 : R) := *)
(*     RM<r1> === RM<r2>. *)
(*   Global Notation " a '|>=' u = v " := *)
(*     (Rmodels_eq a u v)(at level 25, u at next level). *)
(*   Global Notation " a '|>=' u <> v " := *)
(*     (~Rmodels_eq a u v)(at level 25, u at next level). *)

(*   Definition Rmodels_list (RM : Rmodel) (l : list (R * R)) := *)
(*     forall u v, List.In (u, v) l -> RM |>= u = v. *)
(*   Definition Rentails (l : list (R * R)) (u v : R) := *)
(*     forall RM, Rmodels_list RM l -> RM |>= u = v. *)
(*   Global Notation " E |>- u = v " := *)
(*     (Rentails E u v)(at level 25, u at next level). *)

(*   (** Basic morphisms and equivalence properties *) *)
(*   Instance Rmodel_of_m : *)
(*     Morphisms.Morphism (@Logic.eq _ ==> _eq ==> _eq) Rmodel_of. *)
(*   Proof. *)
(*     intros RM RM' HRM r r' Hr; subst; unfold Rmodel_of; *)
(*       inversion_clear Hr; simpl fst; simpl snd. *)
(*     apply fold_m; auto. *)
(*     repeat intro; rewrite H1, H2, H3; reflexivity. *)
(*   Qed. *)
(*   Instance Rmodels_eq_m : *)
(*     Morphisms.Morphism (@Logic.eq _ ==> _eq ==> _eq ==> iff) Rmodels_eq. *)
(*   Proof. *)
(*     repeat intro; unfold Rmodels_eq in *. *)
(*     rewrite H0, H1; subst; reflexivity. *)
(*   Qed. *)
(*   Instance Rmodel_of_Equal_m : *)
(*     Morphisms.Morphism (@Logic.eq _ ==> prod_eq _eq Equal ==> _eq) Rmodel_of. *)
(*   Proof. *)
(*     intros RM RM' HRM r r' Hr; subst; unfold Rmodel_of; *)
(*       inversion_clear Hr; simpl fst; simpl snd. *)
(*     transitivity (fold (sum RM') b c). *)
(*     refine (MapFacts.fold_init _ _ H); eauto with typeclass_instances. *)
(*     repeat intro; subst; rewrite H1, H3; reflexivity. *)
(*     refine (MapFacts.fold_Equal _ _ _ c H0). *)
(*     eauto with typeclass_instances. *)
(*     repeat intro; rewrite H1, H2, H3; reflexivity. *)
(*     repeat intro; ring. *)
(*   Qed. *)

(*   Property Rmodels_refl : forall RM r, RM |>= r = r. *)
(*   Proof. *)
(*     intros; reflexivity. *)
(*   Qed. *)
(*   Property Rmodels_sym : forall RM r r', RM |>= r = r' -> RM |>= r' = r. *)
(*   Proof. *)
(*     intros; symmetry; assumption. *)
(*   Qed. *)
(*   Property Rmodels_trans : forall RM r r' r'', *)
(*     RM |>= r = r' -> RM |>= r' = r'' -> RM |>= r = r''. *)
(*   Proof. *)
(*     intros; unfold Rmodels_eq in *. *)
(*     apply transitivity with (RM<r'>); assumption. *)
(*   Qed. *)

(*   Property Rentails_refl : forall E r r', r === r' -> E |>- r = r'. *)
(*   Proof. *)
(*     repeat intro; rewrite H; apply Rmodels_refl. *)
(*   Qed. *)
(*   Property Rentails_sym : forall E r r', E |>- r = r' -> E |>- r' = r. *)
(*   Proof. *)
(*     intros E r r' H RM HRM; apply Rmodels_sym; auto. *)
(*   Qed. *)
(*   Property Rentails_trans : forall E r r' r'', *)
(*     E |>- r = r' -> E |>- r' = r'' -> E |>- r = r''. *)
(*   Proof. *)
(*     repeat intro; apply Rmodels_trans with r'; auto. *)
(*   Qed. *)

(*   (** Interpretation of polynoms constructors *) *)
(*   Property interp_R0 : forall RM, RM<R0> === 0. *)
(*   Proof. *)
(*     intros; reflexivity. *)
(*   Qed. *)
(*   Property interp_pair : forall RM r c, RM<(c, r)> === c + RM<(0, r)>. *)
(*   Proof. *)
(*     intros; unfold Rmodel_of; simpl. *)
(*     apply MapFacts.fold_rel with (R := fun a b => a === c + b). *)
(*     rewrite Qplus_0_r; reflexivity. *)
(*     intros; rewrite H0; red; ring. *)
(*   Qed. *)
(*   Property interp_empty : forall RM c, RM<(c, [])> === c. *)
(*   Proof. *)
(*     reflexivity. *)
(*   Qed. *)
    
(*   Remark interp_m (RM : Rmodel) : *)
(*     Morphisms.respectful _eq (_eq ==> _eq ==> _eq) (sum RM) (sum RM). *)
(*   Proof. *)
(*     repeat intro; rewrite H, H0, H1; reflexivity. *)
(*   Qed. *)
(*   Remark interp_equiv (RM : Rmodel) : Morphisms.Morphism *)
(*     (_eq ==> @Logic.eq _ ==> Equivalence.equiv ==> Equivalence.equiv) *)
(*     (sum RM). *)
(*   Proof. *)
(*     repeat intro; rewrite H, H0, H1; reflexivity. *)
(*   Qed. *)
(*   Remark interp_transp (RM : Rmodel) : *)
(*     MapFacts.transpose_neqkey Equivalence.equiv (sum RM). *)
(*   Proof. *)
(*     repeat intro; red; ring. *)
(*   Qed. *)
(*   Hint Resolve interp_equiv interp_transp. *)

(*   Property interp_mult_aux : *)
(*     forall RM c r, c =/= 0 -> RM<mult c r> === c * RM<r>. *)
(*   Proof. *)
(*     intros RM c r Hc; destruct (mult_dec c r); unfold Rmodel_of; *)
(*       destruct r as [c' r']; simpl in *. *)
(*     revert rm Hmult_poly. *)
(*     apply MapFacts.fold_rec_bis with (P := fun mvu a => *)
(*       forall rm, (forall t v, MapsTo t v rm <-> is_mult_of c t v mvu) -> *)
(*         fold (sum RM) rm rc === c * a). *)
(*     (* - morphism *) *)
(*     intros; apply H0; clear H0. *)
(*     intros; rewrite H1; split; intro Z; inversion Z. *)
(*     rewrite <- H in H3; exists q; intuition. *)
(*     rewrite H in H3; exists q; intuition. *)
(*     (* - empty *) *)
(*     intros; simpl. *)
(*     rewrite MapFacts.fold_Empty; eauto with typeclass_instances. *)
(*     intros k v Hkv; rewrite H in Hkv; inversion Hkv. *)
(*     contradiction (empty_1 H2). *)
(*     (* - add *) *)
(*     intros; rewrite Qmult_plus_distr_r, <- (H1 (remove k rm)). *)
(*     assert (Heq : rm === (remove k rm)[k <- c * e]). *)
(*     intros k' v'; split; intros [v'' [Hvv'' Hv'']]. *)
(*     destruct (eq_dec k k'). *)
(*     rewrite <- H3, H2 in Hv''; inversion_clear Hv''. *)
(*     apply find_1 in H6; rewrite MapFacts.add_eq_o in H6; auto. *)
(*     inversion H6; subst. *)
(*     exists (c * q); split; auto; apply add_1; auto. *)
(*     exists v''; split; auto; apply add_2; auto; apply remove_2; auto. *)
(*     rewrite MapFacts.add_mapsto_iff, MapFacts.remove_mapsto_iff in Hv''. *)
(*     destruct Hv''. *)
(*     destruct H3; subst; exists (c*e); split; auto. *)
(*     rewrite H2; exists e; auto; apply add_1; auto. *)
(*     exists v''; split; tauto. *)
(*     transitivity (fold (sum (RM)) (remove k rm)[k <- c*e] rc). *)
(*     apply fold_m with (A_OT := Q_OrderedType); auto using interp_m. *)
(*     rewrite MapFacts.fold_add; auto. *)
(*     rewrite !Qmult_assoc, (Qmult_comm (RM k) c); reflexivity. *)
(*     eauto with typeclass_instances. *)
(*     apply remove_1; reflexivity. *)
(*     intros; rewrite MapFacts.remove_mapsto_iff, H2; clear H2 H1. *)
(*     split; intro Z; inversion_clear Z. *)
(*     inversion_clear H2; exists q; auto; apply add_3 with k e; assumption. *)
(*     cut (k =/= t); [intro cut; split; auto|]. *)
(*     exists q; auto; apply add_2; assumption. *)
(*     intro abs; apply H0; rewrite abs; exists q; assumption. *)
(*   Qed. *)
(*   Corollary interp_mult : forall RM c r, RM<mult c r> === c * RM<r>. *)
(*   Proof. *)
(*     intros; generalize (interp_mult_aux RM c r). *)
(*     unfold mult; destruct (eq_dec c 0). *)
(*     intros _; rewrite interp_R0, H, Qmult_0_l; reflexivity. *)
(*     auto. *)
(*   Qed. *)

(*   Property interp_add_monome : *)
(*     forall RM t coef p, RM<add_monome t coef p> === coef * RM t + RM<p>. *)
(*   Proof. *)
(*     intros; destruct (add_monome_dec t coef p); unfold Rmodel_of; *)
(*       destruct p as [cp mp]; simpl in *. *)
(*     destruct (mp[t]) as [q|]_eqn:Ht. *)
(*     (* - adjust *) *)
(*     assert (Heq1 : _eq mp (remove t mp)[t <- q]). *)
(*       intros k v; split; intros [v' [Hvv' Hv']]. *)
(*       destruct (eq_dec t k). *)
(*       exists q; split. *)
(*       apply find_1 in Hv'; rewrite H, Hv' in Ht; inversion Ht; subst; auto. *)
(*       apply add_1; auto. *)
(*       exists v'; split; auto; apply add_2; auto; apply remove_2; auto. *)
(*       rewrite MapFacts.add_mapsto_iff, MapFacts.remove_mapsto_iff in Hv'. *)
(*       destruct Hv'. destruct H; subst; rewrite H in *. *)
(*       exists v'; split; auto; apply find_2; auto. exists v'; intuition. *)
(*     rewrite (fold_m _ _ (interp_m _) _ _ Heq1 _ _ (reflexivity cp)). *)
(*     rewrite MapFacts.fold_add; eauto with typeclass_instances. *)
(*     2:(apply remove_1; reflexivity). *)
(*     assert (Heq2 : _eq rm (remove t mp)[t <- coef + q]). *)
(*       intros k v; split; intros [v' [Hvv' Hv']]. *)
(*       rewrite Hadd_monome_poly in Hv'; inversion_clear Hv'; subst. *)
(*       exists v'; split; auto; apply add_2; intuition; apply remove_2; auto. *)
(*       rewrite H in *; apply find_1 in H0; rewrite H0 in Ht. *)
(*       inversion Ht; subst; exists (coef + q); split; auto; apply add_1; auto. *)
(*       contradiction H0; rewrite H; exists q; apply find_2; auto. *)
(*       rewrite MapFacts.add_mapsto_iff, MapFacts.remove_mapsto_iff in Hv'. *)
(*       destruct Hv'. destruct H; subst; rewrite H in *. *)
(*       exists (coef + q); split; auto; rewrite Hadd_monome_poly. *)
(*       constructor 2 with q; auto; apply find_2; auto. *)
(*       exists v'; split; auto; rewrite Hadd_monome_poly; *)
(*         constructor intuition. *)
(*     rewrite (fold_m _ _ (interp_m _) _ _ Heq2 _ _ (reflexivity cp)). *)
(*     rewrite MapFacts.fold_add; eauto with typeclass_instances. *)
(*     2:(apply remove_1; reflexivity). *)
(*     red; ring. *)
(*     (* - add *) *)
(*     rewrite <- MapFacts.not_find_in_iff in Ht. *)
(*     assert (Heq : _eq rm mp[t <- coef]). *)
(*     repeat intro; split; intros [z [Hvz Hz]]. *)
(*     rewrite Hadd_monome_poly in Hz; inversion_clear Hz; subst. *)
(*     exists z; split; auto; apply add_2; intuition. *)
(*     contradiction Ht; exists q; rewrite <- H; assumption. *)
(*     exists z; split; auto; apply add_1; auto. *)
(*     rewrite MapFacts.add_mapsto_iff in Hz; destruct Hz. *)
(*     destruct H; subst; exists z; split; auto. *)
(*     rewrite Hadd_monome_poly, <- H; constructor 3; auto. *)
(*     exists z; split; auto; rewrite Hadd_monome_poly. *)
(*     constructor 1; intuition. *)
(*     rewrite (fold_m _ _ (interp_m _) _ _ Heq _ _ (reflexivity _)). *)
(*     rewrite MapFacts.fold_add; auto. *)
(*     rewrite Qmult_comm; reflexivity. *)
(*     eauto with typeclass_instances. *)
(*   Qed. *)
(*   Corollary interp_add_monome_m : *)
(*     forall RM t coef m k, RM<(k, add_monome_m t coef m)> === *)
(*       coef * RM t + RM<(k, m)>. *)
(*   Proof. *)
(*     intros; exact (interp_add_monome RM t coef (k, m)). *)
(*   Qed. *)

(*   Property interp_add : forall RM p1 p2, RM<add p1 p2> === RM<p1> + RM<p2>. *)
(*   Proof. *)
(*     intros; unfold add; destruct p1 as [c1 m1]; destruct p2 as [c2 m2]; *)
(*       simpl in *. *)
(*     apply MapFacts.fold_rec_weak with *)
(*       (P := fun mvu a => RM < (c1 + c2, a) > === RM<(c1, mvu)> + RM<(c2, m2)>). *)
(*     (* - morphism *) *)
(*     intros. *)
(*     rewrite H0; apply Qplus_comp_Morphism; try reflexivity. *)
(*     apply Rmodel_of_Equal_m; auto. constructor; auto. *)
(*     (* - empty *) *)
(*     rewrite interp_pair, (interp_pair _ m2 c2), interp_empty. *)
(*     symmetry; apply Qplus_assoc. *)
(*     (* - add *) *)
(*     intros. *)
(*     rewrite interp_add_monome_m, H0; clear H0. *)
(*     rewrite Qplus_assoc; apply Qplus_comp_Morphism; [|reflexivity]. *)
(*     unfold Rmodel_of; simpl; symmetry. *)
(*     rewrite MapFacts.fold_add; auto. *)
(*     rewrite Qmult_comm; reflexivity. *)
(*     eauto with typeclass_instances. *)
(*   Qed. *)

(*   Property interp_choose : forall RM c p, choose p = None -> RM<(c, p)> === c. *)
(*   Proof. *)
(*     intros RM c p Hch; destruct (choose_dec p); try discriminate. *)
(*     unfold Rmodel_of; simpl; revert Hchoose. *)
(*     apply MapFacts.fold_rec_weak with (P := fun mvu a => *)
(*       (forall k v, MapsTo k v mvu -> v === 0) -> a === c). *)
(*     intros; apply H0; intros; rewrite H in H2; apply H1 with k; auto. *)
(*     reflexivity. *)
(*     intros. *)
(*     rewrite (H1 k e) by (apply add_1; auto). *)
(*     rewrite H0; [red; ring|]. *)
(*     intros k' v' H'; apply (H1 k' v'); apply add_2; auto. *)
(*     intro abs; apply H; rewrite abs; exists v'; assumption. *)
(*   Qed. *)

(*   Property interp_embed : forall RM t, RM<embed t> === RM t. *)
(*   Proof. *)
(*     intros; unfold embed; unfold Rmodel_of; simpl. *)
(*     rewrite MapFacts.fold_add; eauto with typeclass_instances. *)
(*     rewrite MapFacts.fold_Empty; eauto with typeclass_instances. *)
(*     red; ring. *)
(*     apply empty_1. *)
(*     intros [z Hz]; apply (empty_1 Hz). *)
(*   Qed. *)

(*   Property interp_subst_embed : *)
(*     forall RM t P r, RM t === RM<P> -> RM<subst (embed t) P r> === RM<r>. *)
(*   Proof. *)
(*     intros; unfold subst. *)
(*     rewrite extract_embed. *)
(*     destruct r as [c m]; simpl in *. *)
(*     destruct m[t] as [qt|]_eqn:Ht; auto. *)
(*     rewrite interp_add, interp_mult, <- H; simpl. *)
(*     unfold Rmodel_of; simpl. *)
(*     assert (Heq : Equal m (remove t m)[t <- qt]). *)
(*     intro k; destruct (eq_dec k t). *)
(*     rewrite H0 in *; rewrite MapFacts.add_eq_o; auto. *)
(*     rewrite MapFacts.add_neq_o, MapFacts.remove_neq_o; auto. *)
(*     intro abs; auto. intro abs; auto. *)
(*     symmetry; rewrite (MapFacts.fold_Equal (eqA:=Qeq)); *)
(*       [| | | |apply Heq]; eauto with typeclass_instances. *)
(*     rewrite MapFacts.fold_add; eauto with typeclass_instances. *)
(*     rewrite Qmult_comm; reflexivity. *)
(*     apply remove_1; auto. *)
(*   Qed. *)
(*   Corollary interp_subst : *)
(*     forall RM p P r, RM<p> === RM<P> -> RM<r> === RM<subst p P r>. *)
(*   Proof. *)
(*     intros; unfold subst. *)
(*     destruct (extract_dec p); auto. *)
(*     assert (Hsubst := interp_subst_embed RM t P r). *)
(*     destruct (snd r)[t] as [ ]_eqn:Ht; auto. *)
(*     rewrite interp_add, interp_mult; destruct r as [cr mr]; simpl in *. *)
(*     rewrite H0 in H; clear p H0. *)
(*     rewrite <- Hsubst. *)
(*     unfold subst; rewrite extract_embed; simpl; rewrite Ht. *)
(*     rewrite interp_add, interp_mult; reflexivity. *)
(*     rewrite interp_embed in H; exact H. *)
(*   Qed. *)
(*   Theorem Rentails_subst : *)
(*     forall E p P r, E |>- p = P -> E |>- r =  subst p P r. *)
(*   Proof. *)
(*     intros E p P r H RM HRM. *)
(*     apply interp_subst; exact (H RM HRM). *)
(*   Qed. *)

(*   Property interp_solve_Solved : *)
(*     forall u v, solve u v = Solved _ -> forall RM, RM |>= u = v. *)
(*   Proof. *)
(*     intros; unfold solve in *. *)
(*     assert (Hm := interp_mult RM (-(1)) v). *)
(*     assert (Ha := interp_add RM u (mult (- (1)) v)). *)
(*     destruct (mult (-(1)) v) as [q1 m1]. *)
(*     destruct (add u (q1, m1)) as [q2 m2]. *)
(*     assert (Hch := interp_choose RM q2 m2). *)
(*     destruct (choose m2) as [[t k]|]; try discriminate. *)
(*     destruct (eq_dec q2 0); try discriminate. *)
(*     rewrite (Hch (refl_equal _)), H0, Hm in Ha; clear H0 Hm Hch. *)
(*     red; rewrite <- (Qplus_0_r (RM<v>)), Ha; red; ring. *)
(*   Qed. *)
(*   Property interp_solve_Unsolvable : *)
(*     forall u v, solve u v = Unsolvable _ -> forall RM, RM |>= u <> v. *)
(*   Proof. *)
(*     intros; unfold solve in *. *)
(*     assert (Hm := interp_mult RM (-(1)) v). *)
(*     assert (Ha := interp_add RM u (mult (- (1)) v)). *)
(*     destruct (mult (-(1)) v) as [q1 m1]. *)
(*     destruct (add u (q1, m1)) as [q2 m2]. *)
(*     assert (Hch := interp_choose RM q2 m2). *)
(*     destruct (choose m2) as [[t k]|]; try discriminate. *)
(*     destruct (eq_dec q2 0); try discriminate. *)
(*     intro Heq; apply H0. *)
(*     rewrite <- (Hch (refl_equal _)), Ha, Hm. *)
(*     red in Heq; rewrite Heq. *)
(*     apply Qplus_opp_r. *)
(*   Qed. *)
(*   Property interp_solve_Subst : *)
(*     forall u v p P, solve u v = Subst p P -> *)
(*       forall RM, RM |>= u = v -> RM |>= p = P. *)
(*   Proof. *)
(*     intros; unfold solve in *. *)
(*     assert (Hm := interp_mult RM (-(1)) v). *)
(*     assert (Ha := interp_add RM u (mult (- (1)) v)). *)
(*     destruct (mult (-(1)) v) as [q1 m1]. *)
(*     destruct (add u (q1, m1)) as [q2 m2]. *)
(*     destruct (choose_dec m2). *)
(*     destruct (eq_dec q2 0); discriminate H. *)
(*     inversion_clear H; subst. *)
(*     red; rewrite interp_embed. *)
(*     rewrite interp_mult; rewrite Hm in Ha; clear Hm. *)
(*     red in H0; rewrite H0, Qplus_opp_r in Ha. *)
(*     assert (Hmult : forall (a b c : Q), a =/= 0 -> a * c === a * b -> c === b). *)
(*     intros; rewrite <- (Qmult_1_l c), <- (Qmult_1_l b). *)
(*     rewrite <- (Qmult_inv_r a); auto. *)
(*     rewrite (Qmult_comm a (/ a)), <- 2Qmult_assoc. *)
(*     apply Qmult_comp; auto; reflexivity. *)
(*     apply (Hmult (-v0)). *)
(*     intro abs. assert (abs' := Qplus_opp_r v0). *)
(*     rewrite abs, Qplus_0_r in abs'; contradiction (H2 abs'). *)
(*     rewrite Qmult_assoc, Qmult_inv_r, Qmult_1_l. *)
(*     assert ((q2, m2) === add_monome k v0 (q2, remove k m2)). *)
(*       constructor; auto. *)
(*       destruct (add_monome_m_dec k v0 (remove k m2)). *)
(*       intros k' v'; split; intros [z [Hzv' Hz]]. *)
(*       destruct (eq_dec k k'). *)
(*       rewrite H in *; exists v0; split; auto. *)
(*       rewrite (MapFacts.MapsTo_fun H1 Hz) in *; auto. *)
(*       rewrite Hadd_monome_m. constructor 3; auto; apply remove_1; auto. *)
(*       exists z; split; auto; rewrite Hadd_monome_m; constructor 1; auto. *)
(*       intro abs; apply H; auto.  apply remove_2; auto. *)
(*       rewrite Hadd_monome_m in Hz; inversion_clear Hz; subst. *)
(*       exists z; split; auto; apply remove_3 with k; auto. *)
(*       contradiction (remove_1 (symmetry H) (m := m2)); exists q; auto. *)
(*       rewrite H in *. exists z; split; auto. *)
(*     rewrite H in Ha. *)
(*     rewrite interp_add_monome in Ha. *)
(*     rewrite <- (Qplus_0_r (-v0 * RM k)), <- Ha. *)
(*     red; field. *)
(*     intro abs. assert (abs' := Qplus_opp_r v0). *)
(*     rewrite abs, Qplus_0_r in abs'; contradiction (H2 abs'). *)
(*   Qed. *)
(*   Theorem Rentails_solve : *)
(*     forall E u v p P, E |>- u = v -> solve u v = Subst p P -> E |>- p = P. *)
(*   Proof. *)
(*     intros E u v p P r H RM HRM. *)
(*     apply interp_solve_Subst with u v; auto. *)
(*   Qed. *)
(* End RModels. *)
Transparent R_OT.

CoInductive subst_spec (t : term) (P r : R) : R -> Prop :=
| subst_spec_intro : 
  forall (rm : R) (Hsubst : forall t', rm t' ===
    if (Some t == t')%compare then r t' * P t' else r t' + r (Some t) * P t'),
  subst_spec t P r rm.
Theorem subst_dec : forall t P r, subst_spec t P r (subst (embed t) P r).
Proof.
  intros t P r; unfold subst; rewrite extract_embed; constructor; intro t'.
  destruct (cancel_dec t r) as [pcr].
  destruct (addk_dec pcr (r (Some t)) P) as [pP].
  destruct t' as [t'|].
  rewrite Hadd, Hcancel_poly.
  destruct (eq_dec (Some t) (Some t')).
  inversion H; subst. unfold is_compare; rewrite (elim_compare_eq H2).
  rewrite H; apply Qplus_0_l.
  destruct (eq_dec t t'). contradiction H; constructor; auto. reflexivity.
  unfold is_compare; rewrite (elim_compare_gt (x:=Some t) (y:=None)).
  rewrite Hadd, Hcancel_coef; reflexivity.
  constructor.
Qed.
CoInductive subst_full_spec (p P r : R) : R -> Prop :=
| subst_spec_normal : 
  forall t (rm : R) 
    (Hp : p === embed t)
    (Hsubst : forall t', rm t' ===
      if (Some t == t')%compare then r t' * P t' else r t' + r (Some t) * P t'),
    subst_full_spec p P r rm
| subst_spec_other : 
  subst_full_spec p P r r.
Corollary subst_full_dec : forall p P r, subst_full_spec p P r (subst p P r).
Proof.
  intros p P r.
  destruct (extract_dec p).
  unfold subst; destruct (extract_dec p).
  constructor 2.
  contradiction (Hnotembed t H).
  constructor 1 with t; auto.
  intro t'; rewrite H; destruct (subst_dec t P r); auto.
Qed.

Corollary subst_linear : forall t P a k b, 
  subst (embed t) P (addk a k b) === 
    addk (subst (embed t) P a) k (subst (embed t) P b).
Proof.
  intros.
  destruct (addk_dec a k b) as [pab].
  destruct (subst_dec t P pab) as [psab].
  destruct (subst_dec t P a) as [psa].
  destruct (subst_dec t P b) as [psb].
  destruct (addk_dec psa k psb) as [psasb].
  intro z; rewrite Hadd0, Hsubst0, Hsubst1, Hsubst.
  destruct (eq_dec (Some t) z); rewrite !Hadd.
  red; ring.
  red; ring.
Qed.

CoInductive solve_basic_spec (u v : R) : Solution R -> Prop :=
| solve_basic_Solved : u === v -> solve_basic_spec u v (Solved _)
| solve_basic_Unsolvable : 
  forall (Hunsolv : forall t, 
    match t with None => u t =/= v t | _ => u t === v t end),
  solve_basic_spec u v (Unsolvable _)
| solve_basic_Subst : 
  forall (t : term) (k : Q) (P : R) 
    (Hk : k =/= 0) (Huvk : u (Some t) === v (Some t) + k)
    (Hsubst : forall t', P t' === 
      if (Some t == t')%compare then 0 else (v t' - u t') / k),
    solve_basic_spec u v (Subst (embed t) P).
Theorem solve_basic_dec : forall u v, solve_basic_spec u v (solve u v).
Proof.
  intros u v; unfold solve.
  destruct (sub_dec u v).
  destruct (choose_dec rm).
  destruct (eq_dec (rm None) 0).
  (* - Solved *)
  constructor.
  destruct (add_const_dec (rm None) (@P0 term term_OT)).
  cut (forall t, u t - v t === 0).
  intros cut t; rewrite <- (Qplus_0_l (v t)), <- (cut t); red; ring.
  intro t; rewrite <- Hsub; rewrite Hchoose.
  destruct t. rewrite Hadd_const_poly; reflexivity.
  rewrite Hadd_const_coef, H; reflexivity.
  (* - Unsolvable *)
  constructor.
  destruct (add_const_dec (rm None) (@P0 term term_OT)).
  assert (cut : forall t, u t === rm t + v t).
  intros t; red; rewrite Hsub; ring.
  destruct t; rewrite cut, Hchoose.
  rewrite Hadd_const_poly; apply Qplus_0_l.
  rewrite Hadd_const_coef, P0_co, Qplus_0_l.
  intro abs; apply H.
  transitivity (v None - v None); do 3 red.
  rewrite <- abs at 1; ring. ring.
  (* - Subst *)
  constructor 3 with v0; subst.
  assumption.
  rewrite Hsub; red; ring.
  intro t; destruct (cancel_dec k rm) as [pc].
  destruct (mult_dec (/ - rm (Some k)) pc) as [pm].
  destruct t as [t|].
  rewrite Hmult, Hcancel_poly.
  destruct (eq_dec (Some k) (Some t)).
  inversion H; subst; unfold is_compare; rewrite elim_compare_eq; auto.
  apply Qmult_0_r.
  destruct (eq_dec k t). contradiction H; constructor; auto.
  rewrite 2Hsub; red; field; rewrite <- Hsub; assumption.
  unfold is_compare; rewrite elim_compare_gt; [|constructor].
  rewrite Hmult, Hcancel_coef, 2Hsub; red; field; rewrite <- Hsub; assumption.
Qed.
Corollary unsolvable_iff : forall (u v : R),
  solve u v = Unsolvable R <-> (forall t, 
    match t with None => u t =/= v t | _ => u t === v t end).
Proof.
  intros; destruct (solve_basic_dec u v); split; intro Hyp.
  discriminate.
  contradiction (Hyp None (H None)).
  exact Hunsolv.
  reflexivity.
  discriminate.
  contradiction Hk; transitivity (u (Some t) - v (Some t)).
  rewrite Huvk; red; ring. 
  assert (H := Hyp (Some t)); simpl in H; rewrite H; red; ring.
Qed.
Corollary solved_iff : forall (u v : R),
  solve u v = Solved R <-> u === v.
Proof.
  intros; destruct (solve_basic_dec u v); split; intro Hyp.
  assumption. reflexivity.
  discriminate. contradiction (Hunsolv None (Hyp None)).
  discriminate.
  contradiction Hk; transitivity (u (Some t) - v (Some t)).
  rewrite Huvk; red; ring.
  rewrite Hyp; red; ring.
Qed.

Theorem iter_as_list :
  forall E f, Theory.iter (Th:=Arith_theory) E = Some f ->
    exists l : list (term * R), forall r,
      f r === fold_right (fun pP acc => 
        subst (embed (fst pP)) (snd pP) acc) r l.
Proof.
  induction E; intros f Hf; simpl in Hf.
  inversion Hf; exists nil; reflexivity.
  destruct a as [a b].
  destruct (Theory.iter E) as [f'|].
  destruct (solve_basic_dec (f' (make a)) (f' (make b))).
  inversion Hf; subst; auto.
  discriminate Hf.
  inversion Hf; subst.
  destruct (IHE f' (refl_equal _)) as [L HL].
  exists ((t, P)::L); intro r; simpl; rewrite HL; reflexivity.
  discriminate Hf.
Qed.
Corollary iter_m : forall E, 
  match Theory.iter (Th:=Arith_theory) E with
    | Some f => Proper (_eq ==> _eq) f
    | None => True
  end.
Proof.
  induction E; simpl.
  repeat intro; auto.
  destruct a as [t1 t2]; destruct (Theory.iter E) as [f|]; auto.
  destruct (solve (f (make t1)) (f (make t2))); auto.
  repeat intro; rewrite H; auto.
Qed.
Corollary iter_linear : forall E f,
  Theory.iter (Th:=Arith_theory) E = Some f ->
  forall a k b, f (addk a k b) === addk (f a) k (f b).
Proof.
  intros E f Hf; destruct (iter_as_list E f Hf) as [L HL].
  clear E Hf; revert f HL; induction L; intros f HL; intros.
  simpl in HL; rewrite !HL; auto.
  rewrite !HL; simpl.
  set (G r := fold_right 
    (fun pP acc => subst (embed (fst pP)) (snd pP) acc) r L) in *.
  fold (G (addk a0 k b)) (G a0) (G b).
  assert (IH := IHL G (fun r => reflexivity _)); clear IHL.
  rewrite IH. apply subst_linear.
Qed.

Section IterOps.
  Variable E : list (term * term).
  Variable f : R -> R.
  Hypothesis Hf : Theory.iter (Th:=Arith_theory) E = Some f.

  Let Ilin := iter_linear E f Hf.
  Local Instance f_m : Proper (_eq ==> _eq) f.
  Proof.
    assert (Im := iter_m E); rewrite Hf in Im; exact Im.
  Qed.

  Implicit Type a b : R.
  Corollary iter_P0 : f (@P0 _ _) === @P0 _ _.
  Proof.
    destruct (iter_as_list E f Hf) as [L HL].
    clear E Hf Ilin; revert f HL; induction L; simpl in *.
    intros; apply HL.
    intros; rewrite HL.
    set (G r := fold_right 
      (fun pP acc => subst (embed (fst pP)) (snd pP) acc) r L) in *.
    fold (G (@P0 _ _)).
    assert (IH := IHL G (fun r => reflexivity _)); clear IHL.
    rewrite IH; destruct (subst_dec (fst a) (snd a) (@P0 _ _)).
    intro z; rewrite Hsubst.
    destruct (eq_dec (Some (fst a)) z).
    rewrite !P0_co; red; ring.
    rewrite !P0_co; red; ring.
  Qed.
  Corollary iter_Pz : forall z, f (@Pz _ _ z) === @Pz _ _ z.
  Proof.
    intro z; destruct (iter_as_list E f Hf) as [L HL].
    clear E Hf Ilin; revert f HL; induction L; simpl in *.
    intros; apply HL.
    intros; rewrite HL.
    set (G r := fold_right 
      (fun pP acc => subst (embed (fst pP)) (snd pP) acc) r L) in *.
    fold (G (@Pz _ _ z)).
    assert (IH := IHL G (fun r => reflexivity _)); clear IHL.
    rewrite IH; destruct (subst_dec (fst a) (snd a) (@Pz _ _ z)).
    intro z'; rewrite Hsubst.
    destruct (eq_dec (Some (fst a)) z').
    destruct z'. rewrite !Pz_co; red; ring. inversion H.
    rewrite !Pz_co; red; ring. 
  Qed.
  Corollary iter_Pq : forall q, f (@Pq _ _ q) === @Pq _ _ q.
  Proof.
    intro q; destruct (iter_as_list E f Hf) as [L HL].
    clear E Hf Ilin; revert f HL; induction L; simpl in *.
    intros; apply HL.
    intros; rewrite HL.
    set (G r := fold_right 
      (fun pP acc => subst (embed (fst pP)) (snd pP) acc) r L) in *.
    fold (G (@Pq _ _ q)).
    assert (IH := IHL G (fun r => reflexivity _)); clear IHL.
    rewrite IH; destruct (subst_dec (fst a) (snd a) (@Pq _ _ q)).
    intro q'; rewrite Hsubst.
    destruct (eq_dec (Some (fst a)) q').
    destruct q'. rewrite !Pq_co; red; ring. inversion H.
    rewrite !Pq_co; red; ring.
  Qed.

  Corollary iter_mult : forall k a, f (mult k a) === mult k (f a).
  Proof.
    Lemma mult_as_addk : forall k a, mult k a === addk (@P0 _ _) k a.
    Proof.
      intros k a z.
      rewrite mult_co, addk_co, P0_co; red; ring.
    Qed.
    intros k a.
    rewrite (mult_as_addk k a), Ilin, mult_as_addk.
    rewrite iter_P0; reflexivity.
  Qed.

  Corollary iter_add : forall a b, f (add a b) === add (f a) (f b).
  Proof.
    Lemma add_as_addk : forall a b, add a b === addk a 1 b.
    Proof.
      intros a b z; rewrite add_co, addk_co; red; ring.
    Qed.
    intros a b.
    rewrite (add_as_addk a b), Ilin, add_as_addk; reflexivity.
  Qed.
  Corollary iter_sub : forall a b, f (sub a b) === sub (f a) (f b).
  Proof.
    Lemma sub_as_addk : forall a b, sub a b === addk a (- (1)) b.
    Proof.
      intros a b z; rewrite sub_co, addk_co; red; ring.
    Qed.
    intros a b.
    rewrite (sub_as_addk a b), Ilin, sub_as_addk; reflexivity.
  Qed.

  Corollary iter_cancel : forall t a, f (cancel t a) ===
    addk (f a) (- a (Some t)) (f (embed t)).
  Proof.
    Lemma cancel_as_addk : forall t a, 
      cancel t a === addk a (-a (Some t)) (embed t).
    Proof.
      intros t a z; rewrite cancel_co, addk_co, embed_co.
      destruct (eq_dec (Some t) z); destruct (eq_dec z (Some t)).
      rewrite H; red; ring.
      contradiction H0; auto.
      contradiction H; auto.
      red; ring.
    Qed.
    intros t a.
    rewrite cancel_as_addk, Ilin; reflexivity.
  Qed.

  Lemma add_monome_as_addk : forall coef t a,
    add_monome t coef a === addk a coef (embed t).
  Proof.
    intros coef t a z; rewrite add_monome_co, addk_co, embed_co.
    destruct (eq_dec (Some t) z); destruct (eq_dec z (Some t)); 
      try (red; ring).
    contradiction H0; auto. contradiction H; auto.
  Qed.
  Lemma add_const_as_addk : forall c a,
    add_const c a === addk a c (@P1 _ _).
  Proof.
    intros c a z; rewrite add_const_co, addk_co, P1_co.
    destruct z; red; ring.
  Qed.
End IterOps.

Theorem iter_preserves_unsolvable : 
  forall l f (u v : R), 
    solve u v = Unsolvable R -> Theory.iter (Th:=Arith_theory) l = Some f ->
    solve (f u) (f v) = Unsolvable R.
Proof.
  induction l; intros f u v Huv Hiter; simpl in Hiter.
  inversion Hiter; exact Huv.
  destruct a as [a b].
  assert (IH := fun f => IHl f u v); clear IHl.
  destruct (Theory.iter l) as [fl|]; [|discriminate].
  destruct (solve_basic_dec (fl (make a)) (fl (make b))); try discriminate.
  inversion Hiter; subst; exact (IH f Huv (refl_equal _)).
  assert (IH' := IH fl Huv (refl_equal _)); clear Huv IH.
  inversion Hiter; subst; simpl in *; clear Hiter.
  destruct (subst_dec t P (fl u)); destruct (subst_dec t P (fl v)).
  rewrite unsolvable_iff in IH' |- *.
  intro z; assert (Hz := IH' z); assert (Ht := IH' (Some t));
    clear IH'; destruct z as [z |]; simpl in Ht.
  rewrite Hsubst0, Hsubst1.
  destruct (eq_dec (Some t) (Some z)).
  rewrite Hz; reflexivity. rewrite Hz, Ht; reflexivity.
  intro abs; apply Hz.
  rewrite Hsubst0, Hsubst1 in abs.
  unfold is_compare in abs; rewrite elim_compare_gt in abs; [|constructor].
  rewrite Ht in abs.
  transitivity ((fl u None + fl v (Some t) * P None) - fl v (Some t) * P None).
  red; ring. rewrite abs; red; ring.
Qed.
Corollary iter_unsolvable_None :
  forall l u v, implyX (Th:=Arith_theory) l u v -> 
    solve u v = Unsolvable R -> Theory.iter l = None.
Proof.
  intros; unfold implyX in *.
  assert (iterm := iter_m l).
  destruct (Theory.iter l) as [f|]_eqn:Heqf; [|reflexivity].
  assert (Pfuv : f (sub u v) === R0).
  rewrite (iter_sub l f Heqf); intro t;
    rewrite sub_co, P0_co, H; red; ring.
  destruct (solve_basic_dec u v); try discriminate.
  assert (Puv : sub u v === Pq (u None - v None)).
  intro; assert (Ht := Hunsolv t); clear Hunsolv.
  rewrite sub_co, Pq_co; destruct t; auto; rewrite Ht; red; ring.
  contradiction (Hunsolv None).
  rewrite Puv, (iter_Pq l f Heqf) in Pfuv.
  generalize (Pfuv None); rewrite Pq_co, P0_co; clear.
  intro Z; red in Z; red.
  (* bizarre que ca ne marche pas [ring [Z]] ici?? *)
  pose proof (Qplus_comp _ _ Z _ _ (Qeq_refl (v None))).
  ring_simplify in H; exact H.
Qed.
(* An old alternative proof by induction dans rev 429 *)

Theorem solve_dec : forall u v, solve_specs (Th:=Arith_theory) u v (solve u v).
Proof.
  intros u v.
  assert (IUns := fun l => iter_unsolvable_None l u v).
  destruct (solve_basic_dec u v); constructor.
  (* - Solved *)
  assumption.
  (* - Unsolvable *)
  intro abs; exact (Hunsolv None (abs None)).
  intros; unfold implyX; rewrite IUns; auto.
  (* - Subst *)
  intro abs; apply Hk.
  transitivity (u (Some t) - v (Some t)); 
    [rewrite Huvk | rewrite (abs (Some t))]; red; ring.
  simpl; destruct (subst_dec t P u) as [psu]; 
    destruct (subst_dec t P v) as [psv].
  intro z; rewrite Hsubst0, Hsubst1.
  assert (Hz := Hsubst z); clear Hsubst.
  destruct (eq_dec (Some t) z); rewrite Hz.
  red; ring.
  rewrite Huvk; red; field; auto.
  simpl; unfold leaves; destruct (FULL.leaves P) as [ ]_eqn.
  intro abs; inversion abs; subst.
  assert (H := H0 (Some t)).
  rewrite embed_co in H; unfold is_compare in H;
    rewrite elim_compare_eq in H; [|reflexivity].
  discriminate H.
  inversion H0.
  rewrite <- Heql, (leaves_iff P t), Hsubst.
  unfold is_compare; rewrite elim_compare_eq; [|reflexivity].
  intro abs; apply abs; reflexivity.
Qed.

Lemma addk_cancel_embed : forall (a : R) (t : term),
  a === addk (cancel t a) (a (Some t)) (embed t).
Proof.
  intros; intro z.
  rewrite addk_co, cancel_co, embed_co.
  unfold is_compare.
  destruct (compare_dec (Some t) z).
  rewrite elim_compare_gt; auto. red; ring.
  rewrite elim_compare_eq; auto; rewrite H; red; ring.
  rewrite elim_compare_lt; auto; red; ring.
Qed.
Theorem implyX_specs : implyX_Specs (Th:=Arith_theory).
Proof.
  constructor.
  (* - Subst *)
  intros; unfold implyX in *; simpl in *.
  assert (Im := iter_m l).
  assert (Ilin := iter_linear l).
  unfold subst in H0; destruct (extract_dec p);
    destruct (Theory.iter l) as [f|]; auto.
  rewrite H0; reflexivity.
  rewrite (addk_cancel_embed a t).
  rewrite H0, !Ilin; auto.
  rewrite <- H, <- H1; reflexivity.
  (* - Solve *)
  intros; unfold implyX in *; simpl in *.
  assert (Im := iter_m l).
  assert (Ilin := iter_linear l).
  unfold solve in H0.
  destruct (choose_dec (sub u v)).
  destruct (eq_dec (sub u v None) 0); inversion H0.
  inversion H0; subst.
  destruct (Theory.iter l)as [f|]_eqn:Hf; auto.
  rewrite <- H6, <- H8; clear H8 H6.
  rewrite (iter_mult _ _ Hf), (iter_cancel _ _ Hf), (iter_sub _ _ Hf).
  set (h := f (embed k)) in *; clearbody h.
  set (k' := (sub u v (Some k))) in *; clearbody k'.
  intro z; rewrite mult_co, addk_co, sub_co, H.
  red; field; auto.
Qed.

Section ZEntailment.
  Import SemLazy.SEMLAZY.
  Variable M : model.
  Open Scope sem_scope.

  Let vty : type_env := Ergo.varmaps_vty M.
  Let vsy : term_env vty := Ergo.varmaps_vsy M.

(*   Notation "t :> ty" := (has_type vty vsy t ty = true)(at level 65). *)
(*   Notation "t :/> ty" := (has_type vty vsy t ty = false)(at level 65). *)

  Definition tplus t u :=
    app (Op DomainZ Plus) (tcons t (tcons u tnil)).
  Definition tmult t u :=
    app (Op DomainZ Mult) (tcons t (tcons u tnil)).
  Definition tminus t u :=
    app (Op DomainZ Minus) (tcons t (tcons u tnil)).
  Definition topp t :=
    app (Op DomainZ Opp) (tcons t tnil).
  Notation "t [+] u" := (tplus t u)(at level 24).
  Notation "t [-] u" := (tminus t u)(at level 23).
  Notation "t [*] u" := (tmult t u)(at level 22).
  Notation "[ z ]" := (app (Cst DomainZ (z%Z)) tnil).

  Variable models_ring : @Ring_theory.ring_theory 
    term ([0]) ([1]) tplus tmult tminus topp (models_eq M).
  Variable models_integral : forall k v w, 
    M |= [k] [*] v = [k] [*] w -> k =/= 0%Z -> M |= v = w.
(*   Print Ring_theory.ring_theory. *)

  Instance models_eq_Refl : Reflexive (models_eq M).
  Proof. exact (models_eq_refl M). Qed.
  Instance models_eq_Sym : Symmetric (models_eq M).
  Proof. exact (models_eq_sym M). Qed.
  Instance models_eq_Trans : Transitive (models_eq M).
  Proof. exact (models_eq_trans M). Qed.

  Instance tplus_m : Proper
    (models_eq M ==> models_eq M ==> models_eq M) tplus.
  Proof.
    repeat intro.
    apply models_eq_congr; repeat (constructor; auto).
  Qed.
  Instance tmult_m : Proper
    (models_eq M ==> models_eq M ==> models_eq M) tmult.
  Proof.
    repeat intro.
    apply models_eq_congr; repeat (constructor; auto).
  Qed.
  Instance tminus_m : Proper
    (models_eq M ==> models_eq M ==> models_eq M) tminus.
  Proof.
    repeat intro.
    apply models_eq_congr; repeat (constructor; auto).
  Qed.
  Instance topp_m : Proper
    (models_eq M ==> models_eq M) topp.
  Proof.
    repeat intro.
    apply models_eq_congr; repeat (constructor; auto).
  Qed.
  Add Ring models_eq_Ring : models_ring (abstract).
  Ltac mring := simpl; ring.

  Goal forall t t', M |= t [+] t' [-] [0] = t' [+] t.
  Proof. intros; mring. Qed.

  (* Lemmas to manipulate arithmetic equalities on terms *)
  Remark push_right_eq : forall t t', M |= t = t' <-> M |= [0] = t [-] t'.
  Proof.
    intros; split; intro.
    assert (M |= [0] = t [-] t) by mring.
    rewrite H0; apply models_eq_congr; repeat (constructor; auto).
    symmetry; rewrite <- (Ring_theory.Radd_0_l models_ring t').
    rewrite (tplus_m _ _ H _ _ (reflexivity _)). mring.
  Qed.
  Property topp_const : forall k, M |= [- k] = topp ([k]).
  Proof.
    intros; rewrite models_eq_iff; reflexivity.
  Qed.
  Remark push_tminus_tmult : forall t u v, 
    M |= (t [-] u)[*] v = t [*] v [-] u [*] v.
  Proof. 
    intros; mring. 
  Qed.
  Remark tplus_0_equal : forall t u,
    M |= u = [0] -> M |= t = t [+] u.
  Proof.
    intros; transitivity (t [+] [0]). mring. 
    symmetry; apply models_eq_congr; repeat (constructor; auto).
  Qed.
  Remark tmult_0_equal : forall t u,
    M |= u = [0] -> M |= t [*] u = [0].
  Proof.
    intros; transitivity (t [*] [0]).
    apply models_eq_congr; repeat (constructor; auto).
    mring.
  Qed.
  Remark push_addk : forall t u v, 
    M |= [t + u * v] = [t] [+] [u] [*] [v].
  Proof.
    intros; simpl.
    rewrite models_eq_iff by reflexivity.
    assert (has_type (Ergo.varmaps_vty M) (Ergo.varmaps_vsy M)
      ([t + u * v]) (typeArith DomainZ) = true).
    reflexivity.
    assert (has_type (Ergo.varmaps_vty M) (Ergo.varmaps_vsy M)
      ([t] [+] [u] [*] [v]) (typeArith DomainZ) = true).
    reflexivity.
    rewrite <- (@replace' _ _ _ _ (typeArith DomainZ) H H0).
    reflexivity.
  Qed.
  Remark push_mult : forall u v, M |= [u * v] = [u] [*] [v].
  Proof.
    intros; simpl.
    rewrite models_eq_iff by reflexivity.
    assert (has_type (Ergo.varmaps_vty M) (Ergo.varmaps_vsy M)
      ([u * v]) (typeArith DomainZ) = true).
    reflexivity.
    assert (has_type (Ergo.varmaps_vty M) (Ergo.varmaps_vsy M)
      ([u] [*] [v]) (typeArith DomainZ) = true).
    reflexivity.
    rewrite <- (@replace' _ _ _ _ (typeArith DomainZ) H H0).
    reflexivity.
  Qed.
  Remark push_minus : forall u v, M |= [u - v] = [u] [-] [v].
  Proof.
    intros; simpl.
    rewrite models_eq_iff by reflexivity.
    assert (has_type (Ergo.varmaps_vty M) (Ergo.varmaps_vsy M)
      ([u - v]) (typeArith DomainZ) = true).
    reflexivity.
    assert (has_type (Ergo.varmaps_vty M) (Ergo.varmaps_vsy M)
      ([u] [-] [v]) (typeArith DomainZ) = true).
    reflexivity.
    rewrite <- (@replace' _ _ _ _ (typeArith DomainZ) H H0).
    reflexivity.
  Qed.

  Remark models_eq_cst_iff : forall (k k' : Z), M |= [k] = [k'] <-> k = k'.
  Proof.
    intros; split; intro H.
    rewrite models_eq_iff in H by reflexivity.
      assert (wtk : has_type (Ergo.varmaps_vty M) (Ergo.varmaps_vsy M) 
        ([k]) (typeArith DomainZ) = true) by reflexivity.
      assert (wtk' : has_type (Ergo.varmaps_vty M) (Ergo.varmaps_vsy M)
        ([k']) (typeArith DomainZ) = true) by reflexivity.
      rewrite <- (Term.replace' _ _ _ _ _ wtk wtk') in H.
      vm_compute in H; exact H.
    rewrite H; reflexivity.
  Qed.
  Corollary models_neq_cst_iff : 
    forall (k k' : Z), M |= [k] <> [k'] <-> k <> k'%Z.
  Proof.
    intros; split; intros H abs.
    rewrite <- models_eq_cst_iff in abs; auto.
    apply H; rewrite <- models_eq_cst_iff; exact abs.
  Qed.

  Property models_integral' : forall k t', M |= [k] [*] t' = [0] ->
    k =/= 0%Z -> M |= t' = [0].
  Proof.
    intros.
    apply (models_integral k); auto.
    rewrite H; mring.
  Qed.
  
  (* How [make] behaves with respect to arithmetic operations *)
  Section MakeOps.
    Property make_z : forall z, make ([z]) === Pz z.
    Proof.
      intro z; unfold make, mk_term.
      intro z'; rewrite add_const_co, Pz_co; destruct z'.
      reflexivity.
      unfold R0; rewrite P0_co; red; ring.
    Qed.
    
    Require Import TermUtils.
    Property mk_term_acc : forall t c p, 
      mk_term c p t === addk p c (mk_term 1 R0 t).
    Proof.
      induction t using term_terms_rect_default; intros c p.
      (* - Lemma for uninterpreted terms *)
      assert (Hdefault : forall t, 
        add_monome t c p === addk p c (add_monome t 1 R0)).
      intros t z; rewrite addk_co, !add_monome_co.
      destruct (eq_dec (Some t) z).
      unfold R0; rewrite P0_co; red; ring.
      unfold R0; rewrite P0_co; red; ring.
      (* - Case analysis on the head of the term *)
      destruct f; simpl; auto; destruct dom; simpl; auto.
      destruct lt; auto.
      intro z'; rewrite addk_co, !add_const_co.
      destruct z'; unfold R0; rewrite P0_co; red; ring.
      destruct op; repeat (progress (destruct lt; auto)).
      (* -- plus *)
      rewrite (H t0) by intuition.
      rewrite (H t) by intuition.
      symmetry; rewrite (H t0) by intuition.
      generalize (mk_term 1 R0 t); generalize (mk_term 1 R0 t0); intros.
      intro z; rewrite !addk_co; red; ring.
      (* -- minus *)
      rewrite (H t0) by intuition.
      rewrite (H t) by intuition.
      symmetry; rewrite (H t0) by intuition.
      generalize (mk_term 1 R0 t); generalize (mk_term 1 R0 t0); intros.
      intro z; rewrite !addk_co; red; ring.
      (* -- opp *)
      rewrite (H t) by intuition.
      symmetry; rewrite (H t) by intuition.
      generalize (mk_term 1 R0 t); intros.
      intro z; rewrite !addk_co; unfold R0; rewrite P0_co; red; ring.
      (* -- mult *)
      destruct (is_const_dec (mk_term 1 R0 t));
        destruct (is_const_dec (mk_term 1 R0 t0)); auto.
      intro z; rewrite addk_co, !add_const_co; destruct z.
      unfold R0; rewrite P0_co; red; ring.
      unfold R0; rewrite P0_co; red; ring.
      generalize (mk_term 1 R0 t0); intro.
      intro z; rewrite !addk_co; destruct z.
      unfold R0; rewrite P0_co; red; ring.
      unfold R0; rewrite P0_co; red; ring.
      generalize (mk_term 1 R0 t); intro.
      intro z; rewrite !addk_co; destruct z.
      unfold R0; rewrite P0_co; red; ring.
      unfold R0; rewrite P0_co; red; ring.
    Qed.
    Corollary mk_term_make : forall t c p, mk_term c p t === addk p c (make t).
    Proof.
      intros; rewrite mk_term_acc; reflexivity.
    Qed.
    
    Corollary make_tplus : forall t t', 
      make (t [+] t') === add (make t) (make t').
    Proof.
      intros; unfold make at 1; simpl.
      rewrite mk_term_make, add_as_addk; reflexivity.
    Qed.
    Corollary make_tminus : forall t t', 
      make (t [-] t') === sub (make t) (make t').
    Proof.
      intros; unfold make at 1; simpl.
      rewrite mk_term_make, sub_as_addk; reflexivity.
    Qed.
    Corollary make_topp : forall t, make (topp t) === sub R0 (make t).
    Proof.
      intros; unfold make at 1; simpl.
      rewrite mk_term_make, sub_as_addk; reflexivity.
    Qed.

    Remark is_const_const : forall q, 
      is_const (add_const (1 * q) R0) === Some q.
    Proof.
      intro q; destruct (is_const_dec (add_const (1 * q) R0)).
      assert (Hz := His_const None); unfold R0 in Hz.
      rewrite !add_const_co, !P0_co in Hz.
      rewrite !Qplus_0_l, Qmult_1_l in Hz.
      constructor; auto.
      contradiction His_const; intro z; unfold R0; destruct z;
        rewrite !add_const_co, !P0_co; red; ring.
    Qed.
    Corollary make_tmult_1 : forall z t, 
      make ([z] [*] t) === mult (z#1) (make t).
    Proof.
      intros; unfold make at 1; simpl.
      assert (Hz  := is_const_const (z#1)).
      inversion Hz.
      destruct (is_const (add_const (1 * (z # 1)) R0)); subst.
      destruct (is_const_dec (mk_term 1 R0 t)).
      unfold make; rewrite His_const; unfold R0.
      intro z'; rewrite !mult_co, !add_const_co; destruct z'; rewrite !P0_co.
      red; ring. rewrite H1; red; ring.
      unfold make; rewrite mult_as_addk; rewrite H1, Qmult_1_r; reflexivity.
      inversion Hz.
    Qed.
    Corollary make_tmult_2 : forall z t, 
      make (t [*] [z]) === mult (z#1) (make t).
    Proof.
      intros; unfold make at 1; simpl.
      assert (Hz  := is_const_const (z#1)).
      inversion Hz.
      destruct (is_const_dec (mk_term 1 R0 t)).
      destruct (is_const (add_const (1 * (z # 1)) R0)); subst.
      unfold make; rewrite His_const; unfold R0.
      intro z'; rewrite !mult_co, !add_const_co; destruct z'; rewrite !P0_co.
      red; ring. rewrite H1; red; ring.
      unfold make; rewrite His_const, mult_as_addk; subst; unfold R0.
      intro z'; rewrite !addk_co, !add_const_co; destruct z'; rewrite !P0_co.
      red; ring. red; ring.
      destruct (is_const (add_const (1 * (z # 1)) R0)); subst.
      rewrite mult_as_addk; unfold make; rewrite H1, Qmult_1_r; reflexivity.
      inversion Hz.
    Qed.
    Corollary make_tmult_3 : forall z z', make ([z] [*] [z']) === Pz (z * z').
    Proof.
      intros; unfold make at 1; simpl.
      assert (Hz  := is_const_const (z#1)).
      assert (Hz'  := is_const_const (z'#1)).
      destruct (is_const (add_const (1 * (z # 1)) R0)); inversion Hz.
      destruct (is_const (add_const (1 * (z' # 1)) R0)); inversion Hz'.
      subst.
      rewrite H1, H4.
      intro h; unfold R0; destruct h. rewrite !add_const_co; auto.
      rewrite !add_const_co, Pz_co, P0_co.
      rewrite Qplus_0_l, Qmult_1_l. reflexivity.
    Qed.
  End MakeOps.

  (* We are interested in polynoms whose rational coefficients are actually
     relative integers. *)
  Inductive isZ (q : Q) : Prop :=
  | isZ_intro : forall z, q === z#1 -> isZ q.
  Definition isZpoly (r : R) : Prop :=
    forall t, isZ (r t).
  
  Instance isZ_m : Proper (_eq ==> iff) isZ.
  Proof.
    intros x y Heq; split; intros [z Hz]; exists z.
    rewrite <-Heq; auto. rewrite Heq; auto.
  Qed.
  Instance isZpoly_m : Proper (_eq ==> iff) isZpoly.
  Proof.
    intros x y Heq; split; intros H t.
    destruct (H t) as [z Hz]; exists z; rewrite <- Heq; auto.
    destruct (H t) as [z Hz]; exists z; rewrite Heq; auto.
  Qed.
  
  Property isZ_z : forall z, isZ (z # 1).
  Proof. 
    intros; exists z; reflexivity.
  Qed.
  Property isZ_plus : forall q q', isZ q -> isZ q' -> isZ (q + q').
  Proof. 
    intros q q' [z Hz] [z' Hz']; exists (z + z')%Z.
    rewrite Hz, Hz'; red; red; simpl; ring.
  Qed.
  Property isZ_minus : forall q q', isZ q -> isZ q' -> isZ (q - q').
  Proof. 
    intros q q' [z Hz] [z' Hz']; exists (z - z')%Z.
    rewrite Hz, Hz'; red; red; simpl; ring.
  Qed.
  Property isZ_opp : forall q, isZ q -> isZ (- q).
  Proof. 
    intros q [z Hz]; exists (- z)%Z.
    rewrite Hz; red; red; simpl; ring.
  Qed.
  Property isZ_mult : forall q q', isZ q -> isZ q' -> isZ (q * q').
  Proof. 
    intros q q' [z Hz] [z' Hz']; exists (z * z')%Z.
    rewrite Hz, Hz'; red; red; simpl; ring.
  Qed.
  Hint Resolve isZ_z isZ_plus isZ_minus isZ_opp isZ_mult : isZ.
  Ltac isZ := solve [auto 100 with isZ].
  
  Property isZp_R0 : isZpoly R0.
  Proof.
    intro; unfold R0; rewrite P0_co; exists 0%Z; reflexivity.
  Qed.
  Property isZp_P1 : isZpoly (@P1 _ _).
  Proof.
    intro; rewrite P1_co; destruct t; isZ.
  Qed.
  Property isZp_Pz : forall z, isZpoly (@Pz _ _ z).
  Proof.
    intros; intro t; rewrite Pz_co; destruct t; isZ.
  Qed.
  Property isZp_embed : forall t, isZpoly (embed t).
  Proof.
    intros; intro z; rewrite embed_co.
    destruct (eq_dec z (Some t)); isZ.
  Qed.
  Property isZp_addk : forall p c p', isZpoly p -> isZ c -> isZpoly p' -> 
    isZpoly (addk p c p').
  Proof.
    intros; intro t.
    rewrite addk_co.
    destruct (H t); destruct H0; destruct (H1 t).
    rewrite H0, H2, H3; isZ.
  Qed.
  Hint Resolve isZp_R0 isZp_P1 isZp_Pz isZp_embed isZp_addk : isZ.
  
  Corollary isZp_add : forall p p', isZpoly p -> isZpoly p' -> 
    isZpoly (add p p').
  Proof.
    intros; rewrite add_as_addk; isZ.
  Qed.
  Corollary isZp_sub : forall p p', isZpoly p -> isZpoly p' -> 
    isZpoly (sub p p').
  Proof.
    intros; rewrite sub_as_addk; isZ.
  Qed.
  Corollary isZp_opp : forall p, isZpoly p -> isZpoly (sub R0 p).
  Proof.
    intros; rewrite sub_as_addk; isZ.
  Qed.
  Corollary isZp_mult : forall c p, isZ c -> isZpoly p -> isZpoly (mult c p).
  Proof.
    intros; rewrite mult_as_addk; isZ.
  Qed.
  Corollary isZp_cancel : forall t p, isZpoly p -> isZpoly (cancel t p).
  Proof.
    intros; rewrite cancel_as_addk; isZ.
  Qed.
  Corollary isZp_add_monome : forall t c p, isZ c -> isZpoly p -> 
    isZpoly (add_monome t c p).
  Proof.
    intros; rewrite add_monome_as_addk; isZ.
  Qed.
  Corollary isZp_add_const : forall c p, isZ c -> isZpoly p ->
    isZpoly (add_const c p).
  Proof.
    intros; rewrite add_const_as_addk; isZ.
  Qed.
  Hint Resolve isZp_add isZp_sub isZp_opp isZp_mult isZp_cancel
    isZp_add_monome isZp_add_const : isZ.

  Goal isZpoly (addk (add (@P1 _ _) (Pz 2)) (3#1) (sub R0 R0)).
  Proof. isZ. Abort.
    
  (** [make] only interprets integer operations therefore it only
     creates polynoms with integer coefficients. *)
  Theorem isZp_mk_term : forall t c p, isZ c -> isZpoly p -> 
    isZpoly (mk_term c p t).
  Proof.
    induction t using term_terms_rect_default; intros.
    destruct f; simpl; try isZ.
    destruct dom; try isZ; destruct lt; isZ.
    destruct op; destruct dom; try isZ;
      repeat (destruct lt; intuition).
    (* easy proof thanks to isZ, only twitch is is_const returns an integer : *)
    destruct (is_const_dec (mk_term 1 R0 t)).
    assert (Hc0 : isZ c0).
    generalize (His_const None); rewrite add_const_co, P0_co, Qplus_0_l.
    intro Z; rewrite <- Z; apply H; intuition.
    destruct (is_const_dec (mk_term 1 R0 t0)).
    assert (Hc1 : isZ c1).
    generalize (His_const0 None); rewrite add_const_co, P0_co, Qplus_0_l.
    intro Z; rewrite <- Z; apply H; intuition.
    intuition. intuition.
    destruct (is_const_dec (mk_term 1 R0 t0)).
    assert (Hc1 : isZ c0).
    generalize (His_const0 None); rewrite add_const_co, P0_co, Qplus_0_l.
    intro Z; rewrite <- Z; apply H; intuition.
    intuition. intuition.
  Qed.
  Corollary isZp_make : forall t, isZpoly (make t).
  Proof.
    intro; unfold make; apply isZp_mk_term; isZ.
  Qed.
  Hint Resolve isZp_mk_term isZp_make : isZ.

  Property isZp_isZ : forall p t, isZpoly p -> isZ (p (Some t)).
  Proof.
    intros; auto.
  Qed.
  Property subst_as_addk : 
    forall r t P, subst (embed t) P r ===
      addk r (r (Some t)) (sub P (embed t)).
  Proof.
    intros; destruct (subst_dec t P r).
    intro z; rewrite Hsubst, addk_co, sub_co, embed_co.
    destruct (eq_dec (Some t) z).
    destruct (eq_dec z (Some t)); [|false_order].
    rewrite H0. red; ring.
    destruct (eq_dec z (Some t)); [false_order|].
    red; ring.
  Qed.
  Corollary isZp_subst : forall t P r,
    isZpoly P -> isZpoly r -> isZpoly (subst (embed t) P r).
  Proof.
    intros; rewrite subst_as_addk; intuition.
  Qed.
  Hint Resolve isZp_isZ isZp_subst : isZ.
    
  Remark Zify_Q : forall q, Qnum q # 1 === (Zpos (Qden q) # 1) * q.
  Proof.
    intros [n d]; red; red; simpl; destruct n. 
    ring.
    rewrite Zpos_mult_morphism; ring.
    simpl; f_equal; rewrite Pmult_1_r, Pmult_comm; reflexivity.
  Qed.
  Remark Q_cancel : forall q k m, m =/= 0%Z ->
    Qnum q * k # 1 == (m * Zpos (Qden q) * k # 1) * q / (m # 1).
  Proof.
    intros [n d] k m H; red; simpl.
    unfold Qinv; simpl; destruct m.
    contradiction H; reflexivity.
    simpl Qnum; simpl Qden.
    rewrite Zpos_mult_morphism; ring.
    simpl Qnum; simpl Qden.
    rewrite Zpos_mult_morphism.
    rewrite <- (Zopp_involutive (Zneg p)), Zopp_neg.
    ring.
  Qed.
  Remark Q_neq : forall q q', q =/= q' -> 
    (Qnum q * (Zpos (Qden q')) =/= Qnum q' * (Zpos (Qden q)))%Z.
  Proof.
    intros [q d] [q' d'] H; simpl; exact H.
  Qed.

  (* In order to prove the initialization step in [implyX_entails]
     we need to prove that if [make] makes two terms into equal polynoms,
     then the two terms are equal in any model. In order to do this, we
     will use a function from polynoms to terms which builds a canonical term 
     corresponding to a given polynom. This will work only when the
     polynom's coefficients are actually integers. *)
  Require Import Qround TermUtils.
  Definition term_of_R (r : R) : term :=
    [Qfloor (r None)] [+]
    fold (fun v qv acc => [Qfloor qv] [*] v [+] acc) (snd (_this r)) ([0]).

  Transparent coef_of.
  Instance Q2Qc_m : Proper (_eq ==> _eq) Q2Qc.
  Proof.
    repeat intro; simpl; apply Qc_is_canon; simpl; rewrite H; reflexivity.
  Qed.
  Instance term_of_R_m : Proper (_eq ==> _eq) term_of_R.
  Proof.
    intros [r wf] [r' wf'] Heq; unfold term_of_R; simpl.
    set (G := (fun v qv acc => [Qfloor qv][*]v[+]acc)).
    change (RAW.equiv r r') in Heq; rewrite RAW.wf_equiv_iff in Heq; auto.
    inversion Heq; subst; simpl.
    match goal with | |- ?t = ?u => change (t === u) end.
    rewrite H. repeat red; f_equal.
    match goal with | |- ?t = ?u => change (t === u) end.
    refine (RAW.fold_m G G _ b d H0 _ _ (reflexivity _)).
    repeat intro; unfold G; rewrite H1,H2,H3; reflexivity.
  Qed.

  Remark equiv_M : Equivalence (models_eq M).
  Proof. dintuition. Qed.
  Hint Resolve equiv_M : core.

  Property term_of_R_P0 : M |= term_of_R (@P0 _ _) = [0].
  Proof.
    rewrite models_eq_iff; reflexivity.
  Qed.
  Property term_of_R_P1 : M |= term_of_R (@P1 _ _) = [1].
  Proof.
    rewrite models_eq_iff; reflexivity.
  Qed.
  Property term_of_R_Pq : forall q, M |= term_of_R (Pz q) = [q].
  Proof.
    intro z; unfold term_of_R; simpl.
    rewrite MapFacts.fold_Empty; auto.
    rewrite Zdiv_1_r; mring.
    apply empty_1.
  Qed.

  Property term_of_R_embed : forall t, M |= term_of_R (embed t) = t.
  Proof.
    intro t; unfold term_of_R, embed; simpl.
    rewrite (MapFacts.fold_add (elt:=Q) (A:=term) (eqA:=models_eq M)); auto.
    rewrite MapFacts.fold_Empty; auto; try apply empty_1.
    simpl; rewrite !Zdiv_1_r; mring.
    repeat intro; rewrite H, H1; subst; reflexivity.
    repeat intro; mring.
    rewrite MapFacts.empty_in_iff; tauto.
  Qed.

  Property Qfloor_addk : forall q k q',
    isZ q -> isZ k -> isZ q' ->
    Qfloor (q + k * q') = (Qfloor q + Qfloor k * Qfloor q')%Z.
  Proof.
    intros.
    destruct H; destruct H0; destruct H1.
    rewrite H, H0, H1; simpl; rewrite !Zdiv_1_r.
    ring.
  Qed.
  Property Qfloor_mult : forall k q,
    isZ q -> isZ k -> Qfloor (q * k) = (Qfloor q * Qfloor k)%Z.
  Proof.
    intros; destruct H; destruct H0.
    rewrite H, H0; simpl; rewrite !Zdiv_1_r.
    ring.
  Qed.
  Property Qfloor_opp : forall k, isZ k ->
    Qfloor (- k) = Zopp (Qfloor k).
  Proof. 
    intros; destruct H; rewrite H. simpl. rewrite !Zdiv_1_r. ring.
  Qed.
  
  Ltac cut_conj :=
    match goal with
      | |- ?A /\ ?B => assert (cut : A); [ | refine (conj cut _)]
      | _ => idtac
    end.
  Property term_of_R_addk : forall p1 k p2, 
    isZpoly p1 -> isZpoly p2 -> isZ k ->
    M |= term_of_R (addk p1 k p2) = 
      term_of_R p1 [+] [Qfloor k] [*] term_of_R p2.
  Proof.
    intros [p1 wf1] k [p2 wf2] Hp1'' Hp2'' Hk; unfold term_of_R; simpl.
    destruct (RAW.addk_dec p1 k p2); simpl @fst in *; simpl @snd in *.
    rewrite Hknul; simpl; rewrite Zdiv_1_r; mring.
    set (G := (fun v qv acc => [Qfloor qv][*]v[+]acc)) in *.

    assert (Hp1' : isZ (fst p1)) by (exact (Hp1'' None)).
    assert (Hp1 : forall v q, MapsTo v q (snd p1) -> isZ q).
    intros. assert (R := Hp1'' (Some v)); simpl in R.
    rewrite (find_1 H) in R; assumption.
    assert (Hp2' : isZ (fst p2)) by (exact (Hp2'' None)).
    assert (Hp2 : forall v q, MapsTo v q (snd p2) -> isZ q).
    intros. assert (R := Hp2'' (Some v)); simpl in R.
    rewrite (find_1 H) in R; assumption. clear Hp1'' Hp2''.
    rewrite Qfloor_addk by isZ. rewrite push_addk.
    cut (M |= fold G rm ([0]) =
      fold G (snd p1) ([0]) [+] [Qfloor k] [*] fold G (snd p2) ([0])).
    intro cut; rewrite cut; mring.

    revert rm Hp1 Hp2 Haddk_poly; generalize (snd p1) as m1.
    clear Hp1' Hp2'.
    apply MapFacts.fold_rec_weak with
      (P := fun m acc => forall m1 rm
        (HisZ1 : forall v q, MapsTo v q m1 -> isZ q)
        (HisZm : forall v q, MapsTo v q m -> isZ q),
        (forall v q, MapsTo v q rm <-> RAW.is_addk_of v q m1 k m) ->
        M |= fold G rm ([0]) =
          fold G m1 ([0]) [+] [Qfloor k] [*] acc); intros; simpl in *.
    (* - morphism *)
    rewrite H0. reflexivity.
    assumption. intros; rewrite H in H2; eauto.
    intros; rewrite H1.
    split; intro Z; inversion Z.
    constructor 1 with q1 q2; auto; rewrite H; assumption.
    constructor 2; auto; rewrite H; assumption.
    constructor 3 with q2; auto; rewrite H; assumption.
    constructor 1 with q1 q2; auto; rewrite <- H; assumption.
    constructor 2; auto; rewrite <- H; assumption.
    constructor 3 with q2; auto; rewrite <- H; assumption.
    (* - empty *)
    assert (Heq : Equal rm m1).
    intros y; destruct (rm[y]) as [q|]_eqn:Hy.
    rewrite <- MapFacts.find_mapsto_iff, H in Hy.
    inversion Hy; try contradiction (empty_1 H1).
    symmetry; apply find_1; assumption.
    destruct m1[y] as [qy|]_eqn:Hqy; auto.
    rewrite <- MapFacts.not_find_in_iff in Hy; contradiction Hy.
    exists qy; rewrite H; constructor 2.
    apply find_2; assumption. intros [z zabs]; contradiction (empty_1 zabs).
    transitivity (fold G m1 ([0])).
    apply MapFacts.fold_Equal with (eqA := models_eq M); auto.
    repeat intro; unfold G; simpl. rewrite H0, H1, H2; reflexivity.
    repeat intro; unfold G; mring.
    mring.
    (* - add *) (* cette preuve est horrible vraiment il faudrait changer ça *)
    destruct (MapFacts.In_dec m1 k0).
    destruct i as [z Hz].
    symmetry; rewrite MapFacts.fold_Add.
    instantiate (1 := (remove k0 m1)).
      instantiate (1 := z%Q). instantiate (1 := k0).
    destruct (eq_dec (z + k * e) 0).
    unfold G at 1 3; symmetry.
    rewrite (H0 (remove k0 m1)).
    assert (HR : M |= [Qfloor z] [+] [Qfloor k] [*] [Qfloor e] = [0]).
    rewrite <- push_addk, <- Qfloor_addk, H2. reflexivity. 
    eauto. eauto. apply (HisZm k0); apply add_1; reflexivity.
    set (F := fold G (remove k0 m1) ([0])).
    transitivity (([Qfloor z][+][Qfloor k][*][Qfloor e])
      [*]k0[+]F[+][Qfloor k][*]a); [ | mring ].
    symmetry; rewrite push_right_eq.
    transitivity (([Qfloor z][+][Qfloor k][*][Qfloor e])[*]k0); [ | mring ].
    symmetry; rewrite (tmult_m _ _ HR _ _ (reflexivity k0)); mring.
    intros; apply HisZ1 with v; eapply remove_3; apply H3.
    intros; apply HisZm with v. apply add_2; auto.
    intro abs; apply H; exists q; rewrite abs; assumption.
    intros; rewrite H1; split; intro HH; inversion_clear HH.
      destruct (eq_dec v k0).
      rewrite H7 in *; contradiction H6; rewrite H5.
      rewrite (MapFacts.MapsTo_fun H3 Hz).
      rewrite MapFacts.add_mapsto_iff in H4.
      destruct H4. rewrite <- (proj2 H4); assumption.
      contradiction (proj1 H4); reflexivity.
      assert (k0 =/= v) by (intro abs; apply H7; auto).
      constructor 1 with q1 q2; auto.
      apply remove_2; auto. apply add_3 with k0 e; auto.
      assert (k0 =/= v) by (intro abs; apply H4; rewrite abs;
        exists e; apply add_1; auto).
      constructor 2; auto.
      apply remove_2; auto.
      intro abs; apply H4; rewrite MapFacts.add_in_iff; tauto.
      assert (k0 =/= v) by (intro abs; apply H5; rewrite <- abs;
        exists z; auto).
      constructor 3 with q2; auto.
      apply add_3 with k0 e; auto.
      rewrite MapFacts.remove_in_iff; tauto.
      assert (k0 =/= v) by (rewrite MapFacts.remove_mapsto_iff in H3; tauto).
      constructor 1 with q1 q2; auto.
      apply remove_3 with k0; auto.
      apply add_2; auto.
      assert (k0 =/= v) by (rewrite MapFacts.remove_mapsto_iff in H3; tauto).
      constructor 2; auto.
      apply remove_3 with k0; auto.
      rewrite MapFacts.add_in_iff; intros [abs | abs]; auto.
      assert (k0 =/= v) by (intro abs; apply H; rewrite abs; exists q2; auto).
      constructor 3 with q2; auto.
      apply add_2; auto.
      intro abs; apply H5; rewrite MapFacts.remove_in_iff; tauto.

    symmetry; rewrite MapFacts.fold_Add.
    instantiate (1 := (remove k0 rm)).
      instantiate (1 := (z + k * e)%Q). instantiate (1 := k0).
    assert (IH : M |= fold G (remove k0 rm) ([0]) =
      fold G (remove k0 m1) ([0])[+][Qfloor k][*]a); [apply H0|]; clear H0.
    intros; apply HisZ1 with v; eapply remove_3; apply H0.
    intros; apply HisZm with v. apply add_2; auto.
    intro abs; apply H; exists q; rewrite abs; assumption.
    intros; rewrite MapFacts.remove_mapsto_iff; rewrite H1; split; intro HH;
      (destruct HH as [HH1 HH2]; inversion_clear HH2) || inversion_clear HH.
      constructor 1 with q1 q2; auto.
      apply remove_2; auto.
      apply add_3 with k0 e; auto.
      constructor 2; auto.
      apply remove_2; auto.
      intro abs; apply H3; rewrite MapFacts.add_in_iff; auto.
      constructor 3 with q2; auto.
      apply add_3 with k0 e; auto.
      rewrite MapFacts.remove_in_iff; tauto.
      cut_conj. rewrite MapFacts.remove_mapsto_iff in H0; tauto.
      constructor 1 with q1 q2; auto.
      apply remove_3 with k0; auto.
      apply add_2; auto.
      cut_conj. rewrite MapFacts.remove_mapsto_iff in H0; tauto.
      constructor 2; auto.
      apply remove_3 with k0; auto.
      rewrite MapFacts.add_in_iff; intro abs; destruct abs; auto.
      cut_conj. intro abs; apply H; rewrite abs; exists q2; auto.
      constructor 3 with q2; auto.
      apply add_2; auto.
      intro abs; apply H4; rewrite MapFacts.remove_in_iff; auto.
    assert (HR : M |= [Qfloor (z + k * e)] = 
      [Qfloor z] [+] [Qfloor k] [*] [Qfloor e]).
    rewrite Qfloor_addk, push_addk. reflexivity.
    apply HisZ1 with k0; auto. auto. 
    apply HisZm with k0; apply add_1; auto.
    unfold G at 1 3 5.
    rewrite IH, HR; mring.
    auto.
    repeat intro; unfold G; rewrite H3, H4, H5; reflexivity.
    repeat  intro; unfold G; mring.
    apply remove_1; reflexivity.
    intro y; rewrite MapFacts.add_o, MapFacts.remove_o.
    destruct (eq_dec k0 y); [apply find_1 | reflexivity].
    rewrite H1. constructor 1 with z e.
    rewrite <- H3; assumption.
    rewrite MapFacts.add_mapsto_iff; intuition.
    reflexivity. assumption.
    auto.
    repeat intro; unfold G; rewrite H2, H3, H4; reflexivity.
    repeat  intro; unfold G; mring.
    apply remove_1; reflexivity.
    intro y; rewrite MapFacts.add_o, MapFacts.remove_o.
    apply find_1 in Hz; rewrite MapFacts.not_find_in_iff in H.
    destruct (eq_dec k0 y). rewrite <- H2; assumption. reflexivity.

    rewrite MapFacts.fold_Add.
    instantiate (1 := remove k0 rm).
    instantiate (1 := k * e). instantiate (1 := k0).
    assert (IH : M |= fold G (remove k0 rm) ([0]) =
      fold G m1 ([0])[+][Qfloor k][*]a); [apply H0|]; clear H0.
    assumption.
    intros; apply HisZm with v. apply add_2; auto.
    intro abs; apply H; exists q; rewrite abs; assumption.
    intros; rewrite MapFacts.remove_mapsto_iff; rewrite H1; split; intro HH;
      (destruct HH as [HH1 HH2]; inversion_clear HH2) || inversion_clear HH.
      constructor 1 with q1 q2; auto.
      apply add_3 with k0 e; auto.
      constructor 2; auto.
      intro abs; apply H2; rewrite MapFacts.add_in_iff; auto.
      constructor 3 with q2; auto.
      apply add_3 with k0 e; auto.
      cut_conj. intro abs; apply H; rewrite abs; exists q2; auto.
      constructor 1 with q1 q2; auto.
      apply add_2; auto.
      cut_conj. intro abs; apply n; exists q; rewrite abs; auto.
      constructor 2; auto.
      rewrite MapFacts.add_in_iff; intro abs; destruct abs; auto.
      cut_conj. intro abs; apply H; rewrite abs; exists q2; auto.
      constructor 3 with q2; auto.
      apply add_2; auto.
    assert (HR : M |= [Qfloor (k * e)] = [Qfloor k] [*] [Qfloor e]).
    setoid_replace (k * e) with (0 + k * e) by ring.
    rewrite Qfloor_addk, push_addk. simpl; rewrite Zdiv_1_r; mring.
    isZ. isZ. apply HisZm with k0; apply add_1; auto.
    unfold G at 1 4.
    rewrite IH, HR. mring.
    auto.
    repeat intro; unfold G; rewrite H2, H3, H4; reflexivity.
    repeat  intro; unfold G; mring.
    apply remove_1; reflexivity.
    intro y; rewrite MapFacts.add_o, MapFacts.remove_o.
    destruct (eq_dec k0 y); [apply find_1 | reflexivity].
    rewrite H1; constructor 3 with e; auto.
    apply add_1; auto. rewrite <- H2; assumption.
  Qed.

  Corollary term_of_R_mult : forall k p, isZ k -> isZpoly p ->
    M |= term_of_R (mult k p) = [Qfloor k] [*] term_of_R p.
  Proof.
    intros; rewrite mult_as_addk, term_of_R_addk, term_of_R_P0 by isZ; mring.
  Qed.
  Corollary term_of_R_add : forall p1 p2, isZpoly p1 -> isZpoly p2 ->
    M |= term_of_R (add p1 p2) = term_of_R p1 [+] term_of_R p2.
  Proof.
    intros; rewrite add_as_addk, !term_of_R_addk by isZ. 
    simpl; rewrite Zdiv_1_r; mring.
  Qed.
  Corollary term_of_R_sub : forall p1 p2, isZpoly p1 -> isZpoly p2 ->
    M |= term_of_R (sub p1 p2) = term_of_R p1 [-] term_of_R p2.
  Proof.
    intros; rewrite sub_as_addk, !term_of_R_addk by isZ.
    simpl; rewrite Zdiv_1_r.
    transitivity (term_of_R p1 [+] topp (term_of_R p2)); [|mring].
    apply models_eq_congr; do 2 constructor.
    replace (Zneg xH) with (Zopp 1) by reflexivity.
    rewrite topp_const; mring. constructor.
  Qed.
  Corollary term_of_R_cancel : forall t p, isZpoly p ->
    M |= term_of_R (cancel t p) = 
      term_of_R p [-] [Qfloor (p (Some t))] [*] t.
  Proof.
    intros; rewrite cancel_as_addk, term_of_R_addk by isZ.
    destruct (H (Some t)); rewrite H0; simpl; rewrite !Zdiv_1_r.
    rewrite term_of_R_embed, topp_const. mring.
  Qed.
  Corollary term_of_R_add_monome : forall t coef p, isZ coef -> isZpoly p ->
    M |= term_of_R (add_monome t coef p) = term_of_R p [+] [Qfloor coef] [*] t.
  Proof.
    intros; rewrite add_monome_as_addk, term_of_R_addk, term_of_R_embed by isZ.
    mring.
  Qed.
  Corollary term_of_R_add_const : forall c p, isZ c -> isZpoly p ->
    M |= term_of_R (add_const c p) = term_of_R p [+] [Qfloor c].
  Proof.
    intros; rewrite add_const_as_addk, term_of_R_addk, term_of_R_P1 by isZ.
    mring.
  Qed.

  Theorem mk_term_correct : forall t coef p, isZ coef -> isZpoly p ->
    M |= term_of_R (mk_term coef p t) = term_of_R p [+] [Qfloor coef] [*] t.
  Proof.
    (* - Cut for default cases *)
    assert (Hdefault : forall t coef p, isZ coef -> isZpoly p ->
      M |= term_of_R (add_monome t coef p) =
        term_of_R p [+] [Qfloor coef] [*] t)
    by (intros; rewrite term_of_R_add_monome by isZ; reflexivity).
    induction t using term_terms_rect_default; intros; destruct f.
    (* - Unint *)
    simpl; auto.
    (* - Cst *)
    destruct dom; destruct lt; simpl; auto.
    rewrite term_of_R_add_const by isZ.
    apply models_eq_congr; do 2 constructor; auto.
    setoid_replace (coef * (z # 1)) with (0 + coef * (z # 1)) by ring.
    rewrite Qfloor_addk, push_addk by isZ.
    simpl; rewrite !Zdiv_1_r; mring. constructor.
    (* - Op *)
    destruct op; destruct dom; simpl; auto;
      repeat (progress (destruct lt; auto)).
    rewrite (H t0), (H t); try isZ.
    fold (tplus t t0); mring.
    left; reflexivity. right; left; reflexivity.
    rewrite (H t0), (H t); try isZ.
    fold (tminus t t0). rewrite Qfloor_opp, topp_const by isZ; mring.
    left; reflexivity. right; left; reflexivity.
    rewrite (H t); try isZ.
    fold (topp t). rewrite Qfloor_opp, topp_const by isZ; mring.
    left; reflexivity.
    fold (tmult t t0).
    destruct (is_const_dec (mk_term 1 R0 t)); auto.
    assert (Hc : isZ c).
    setoid_replace c with (mk_term 1 R0 t None).
    apply isZp_mk_term; isZ.
    rewrite His_const, add_const_co, P0_co; ring.
    assert (Ht : M |= t = [Qfloor c]).
    transitivity (term_of_R (mk_term 1 R0 t)).
    symmetry; rewrite (H t), term_of_R_P0; try isZ.
    simpl; rewrite Zdiv_1_r; mring. intuition.
    rewrite His_const, term_of_R_add_const, term_of_R_P0; try isZ; mring.
    destruct (is_const_dec (mk_term 1 R0 t0)); auto.
    assert (Hc0 : isZ c0).
    setoid_replace c0 with (mk_term 1 R0 t0 None).
    apply isZp_mk_term; isZ.
    rewrite His_const0, add_const_co, P0_co; ring.
    assert (Ht0 : M |= t0 = [Qfloor c0]).
    transitivity (term_of_R (mk_term 1 R0 t0)).
    symmetry; rewrite (H t0), term_of_R_P0; try isZ.
    simpl; rewrite Zdiv_1_r; mring. intuition.
    rewrite His_const0, term_of_R_add_const, term_of_R_P0; try isZ; mring.
    rewrite term_of_R_add_const, !Qfloor_mult, !push_mult by isZ.
    rewrite <- Ht, <- Ht0; mring.
    rewrite term_of_R_addk, !Qfloor_mult, !push_mult by isZ.
    rewrite (H t0), term_of_R_P0; try isZ.
    simpl; rewrite <- Ht, Zdiv_1_r; mring. intuition.
    destruct (is_const_dec (mk_term 1 R0 t0)); auto.
    assert (Hc : isZ c).
    setoid_replace c with (mk_term 1 R0 t0 None).
    apply isZp_mk_term; isZ.
    rewrite His_const0, add_const_co, P0_co; ring.
    assert (Ht0 : M |= t0 = [Qfloor c]).
    transitivity (term_of_R (mk_term 1 R0 t0)).
    symmetry; rewrite (H t0), term_of_R_P0; try isZ.
    simpl; rewrite Zdiv_1_r; mring. intuition.
    rewrite His_const0, term_of_R_add_const, term_of_R_P0; try isZ; mring.
    rewrite term_of_R_addk; try isZ.
    rewrite Qfloor_mult, push_mult by isZ.
    rewrite (H t), term_of_R_P0; try isZ. 
    simpl; rewrite Zdiv_1_r; rewrite <- Ht0; mring. intuition.
  Qed.
  Corollary make_correct : forall t, M |= term_of_R (make t) = t.
  Proof.
    intro; unfold make; rewrite mk_term_correct by isZ.
    rewrite term_of_R_P0; simpl; rewrite Zdiv_1_r; mring.
  Qed.  
  Corollary make_entails : forall t u, make t === make u -> M |= t = u.
  Proof.
    intros; transitivity (term_of_R (make t)).
    symmetry; apply make_correct.
    transitivity (term_of_R (make u)).
    rewrite H; reflexivity. apply make_correct.
  Qed.

  (* Given a polynom [P] with rational coefficients, we know a certain
     multiple of this polynom has integer coefficients, say [m.P], and
     we can build a term [t] which corresponds to [m.P], ie. such that
     [make t = m.P]. *)
  Definition common_denom (r : R) :=
    (Zpos (Qden (fst (_this r))) *
      fold (fun _ qv acc => (Zpos (Qden qv)) * acc)%Z (snd (_this r)) 1)%Z.
  Lemma common_denom_nonzero : forall r, common_denom r =/= 0%Z.
  Proof.
    intros [[c m] wf]; unfold common_denom; simpl fst; simpl snd; simpl this.
    apply MapFacts.fold_rec_weak with 
      (P := fun m acc => (Zpos (Qden c) * acc =/= 0)%Z).
    intros; auto.
    discriminate.
    intros; destruct a; try discriminate; false_order.
  Qed.
  Lemma common_denom_coef : forall (r : R) t, 
    r t === 0 \/ exists z, common_denom r = (Zpos (Qden (r t)) * z)%Z.
  Proof.
    intros [[c m] wf]; unfold common_denom; simpl fst; simpl snd; simpl this.
    intro t; replace (mk_poly wf t) with (RAW.coef_of (c, m) t) by reflexivity.
    destruct t; simpl RAW.coef_of; [ | right; eexists; eauto].
    apply MapFacts.fold_rec_weak with
      (P := fun m acc => match m[t] with Some q => q | None => 0%Q end === 0%Q
        \/ exists z, (' Qden c * acc = 
        ' Qden (match m[t] with | Some q=> q | None => 0%Q end) * z)%Z).
    intros; destruct H0 as [Hz | [z Hz]]; [left | right]. 
    rewrite <- H; exact Hz. exists z; rewrite <- H; exact Hz.
    rewrite MapFacts.empty_o. left; reflexivity.
    intros; rewrite MapFacts.add_o; destruct (eq_dec k t).
    right; exists ('Qden c * a)%Z; ring.
    destruct H0; [left; exact H0 | right].
    destruct H0 as [z Hz].
    exists (z * 'Qden e)%Z.
    symmetry; rewrite Zmult_assoc, <- Hz; ring.
  Qed.
  Lemma common_denom_isZp : forall r, isZpoly (mult (common_denom r # 1) r).
  Proof.
    intros r t; destruct (common_denom_coef r t); rewrite mult_co.
    exists 0%Z; rewrite H; red; ring.
    destruct H as [z Hz]; rewrite Hz.
    exists (Qnum (r t) * z)%Z; destruct (r t) as [q d].
    red; red; simpl Qden; simpl Qnum; destruct z.
    ring. rewrite Zpos_mult_morphism; ring.
    simpl; destruct q. ring. 
    simpl; f_equal; rewrite Pmult_1_r.
    rewrite Pmult_comm, <- Pmult_assoc, (Pmult_comm p d); reflexivity.
    simpl; rewrite !Zpos_mult_morphism; ring.
  Qed.

  Lemma Qfloor_isZ : forall q, isZ q -> (Qfloor q # 1) === q.
  Proof.
    intros q H; destruct H; rewrite H; simpl.
    rewrite Zdiv_1_r; reflexivity.
  Qed.
  (** The last thing we need in order to prove the theorem [find_multiple_poly]
     is to show that for all polynom [p] with integer coefficients, 
     [make (term_of_R p)] is equal to [p] itself. Unfortunately that is not true
     if [p] has some ill-formed monoms, for example a term [t] equals to a
     constant or any arithmetic expression non reduced to a variable. Therefore
     we need another invariant on the polynom structure, characterizing the 
     form of their monoms. *)
  Definition isM (t : term) :=
    match t with
      | Term.app f l => 
        match f with
          | Unint _ _ => True
          | Cst DomainZ r => 
            match l with
              | nil => False
              | _ => True
            end
          | Op DomainZ Plus => 
            match l with
              | cons t1 (cons t2 nil) => False
              | _ => True
            end
          | Op DomainZ Mult => 
            match l with
              | cons t1 (cons t2 nil) =>
                let p1 := mk_term 1%Q R0 t1 in
                  let p2 := mk_term 1%Q R0 t2 in
                    match is_const p1, is_const p2 with
                      | None, None => True
                      | _, _ => False
                    end
              | _ => True
            end
          | Op DomainZ Minus => 
            match l with
              | cons t1 (cons t2 nil) => False
              | _ => True
            end
          | Op DomainZ Opp => 
            match l with
              | cons t1 nil => False
              | _ => True
            end
          | _ => True
        end
    end.
  Definition isMpoly (p : R) := forall t, p (Some t) =/= 0 -> isM t.
  Instance isMpoly_m : Proper (_eq ==> iff) isMpoly.
  Proof.
    intros; split; repeat intro.
    apply H0; rewrite H; auto. apply H0; rewrite <- H; auto.
  Qed.

  Property isM_make_embed : forall t, isM t -> make t === embed t.
  Proof.
    intros t Ht.
    assert (Hdefault : add_monome t 1 R0 === embed t).
    intro z; rewrite add_monome_co, embed_co.
    destruct (eq_dec (Some t) z); destruct (eq_dec z (Some t)); 
      try order; rewrite P0_co; reflexivity.
    destruct t; destruct f; auto.
    destruct dom; auto.
    destruct lt; simpl in *; auto; contradiction.
    destruct dom; auto.
    destruct op; auto; 
      repeat (destruct lt; simpl in *; auto; try contradiction).
    unfold make; simpl.
    destruct (is_const_dec (mk_term 1 R0 t)); try contradiction Ht.
    destruct (is_const_dec (mk_term 1 R0 t0)); try contradiction Ht.
    assumption.
  Qed.
  Property isM_not_is_const : forall t, isM t -> is_const (make t) = None.
  Proof.
    intros t Ht.
    assert (Hdefault : is_const (add_monome t 1 R0) = None).
    destruct (is_const_dec (add_monome t 1 R0)); auto.
    assert (abs := His_const (Some t)).
    rewrite add_monome_co, add_const_co in abs.
    destruct (eq_dec (Some t) (Some t)). discriminate abs. false_order.
    destruct t; destruct f; auto.
    destruct dom; auto.
    destruct lt; simpl in *; auto; contradiction.
    destruct dom; auto.
    destruct op; auto; 
      repeat (destruct lt; simpl in *; auto; try contradiction).
    unfold make; simpl.
    destruct (is_const_dec (mk_term 1 R0 t)); try contradiction Ht.
    destruct (is_const_dec (mk_term 1 R0 t0)); try contradiction Ht.
    assumption.
  Qed.

  Property isMp_P0 : isMpoly R0.
  Proof. 
    repeat intro; contradiction H; reflexivity.
  Qed.
  Property isMp_P1 : isMpoly R1.
  Proof. 
    repeat intro; contradiction H; reflexivity.
  Qed.
  Property isMp_mult : forall c p, isMpoly p -> isMpoly (mult c p).
  Proof.
    repeat intro; apply H; intro abs; apply H0; rewrite mult_co.
    rewrite abs; red; ring.
  Qed.
  Property isMp_addk : forall p k p', isMpoly p -> isMpoly p' -> 
    isMpoly (addk p k p').
  Proof.
    repeat intro; rewrite addk_co in H1.
    destruct (eq_dec (p (Some t)) 0).
    apply H0. intro abs; apply H1; rewrite H2, abs; red; ring.
    apply H; auto.
  Qed.
  Property isMp_add : forall p p', isMpoly p -> isMpoly p' -> 
    isMpoly (add p p').
  Proof.
    intros; rewrite add_as_addk; apply isMp_addk; auto.
  Qed.
  Property isMp_sub : forall p p', isMpoly p -> isMpoly p' -> 
    isMpoly (sub p p').
  Proof.
    intros; rewrite sub_as_addk; apply isMp_addk; auto.
  Qed.
  Property isMp_add_const : forall c p, isMpoly p -> isMpoly (add_const c p).
  Proof.
    intros; rewrite add_const_as_addk; apply isMp_addk; auto; apply isMp_P1.
  Qed.
  Property isMp_embed : forall t, isM t -> isMpoly (embed t).
  Proof.
    repeat intro; rewrite embed_co in *; destruct (eq_dec (Some t0) (Some t)).
    inversion H1; subst; rewrite H4; assumption.
    contradiction H0; reflexivity.
  Qed.
  Property isMp_add_monome : forall c t p, isMpoly p -> isM t -> 
    isMpoly (add_monome t c p).
  Proof.
    intros; rewrite add_monome_as_addk; apply isMp_addk; auto using isMp_embed.
  Qed.

  Property isMp_mk_term : forall t c p, isMpoly p -> isMpoly (mk_term c p t).
  Proof with (try (apply isMp_add_monome; auto; exact I)).
    induction t using term_terms_rect_default.
    intros; destruct f; simpl...
    destruct dom... destruct lt... apply isMp_add_const; auto.
    destruct dom; destruct op; destruct lt...
    destruct lt... destruct lt... intuition.
    destruct lt... destruct lt... intuition.
    destruct lt... intuition.
    destruct lt... destruct lt...
    destruct (is_const (mk_term 1 R0 t)) as [ ]_eqn:Ht;
      destruct (is_const (mk_term 1 R0 t0)) as [ ]_eqn:Ht0.
    apply isMp_add_const; auto. 
    apply isMp_addk; auto; apply H; intuition; exact isMp_P0.
    apply isMp_addk; auto; apply H; intuition; exact isMp_P0.
    apply isMp_add_monome; auto.
    simpl; rewrite Ht, Ht0; trivial.
  Qed.
  Corollary isMp_make : forall t, isMpoly (make t).
  Proof.
    intros; unfold make; apply isMp_mk_term; auto using isMp_P0.
  Qed.

  Theorem isMp_iter : forall E f, Theory.iter E (Th:=Arith_theory) = Some f ->
    forall p, isMpoly p -> isMpoly (f p).
  Proof.
    induction E; intros; simpl in H; inversion H.
    assumption.
    destruct a as [t1 t2].
    destruct (Theory.iter E); [|discriminate].
    destruct (solve_basic_dec (r (make t1)) (r (make t2))); inversion H; subst.
    apply (IHE f); auto.
    rewrite subst_as_addk; apply isMp_addk; auto.
    apply isMp_sub.
    intro z; rewrite (Hsubst (Some z)).
    destruct (eq_dec (Some t) (Some z)).
    intro abs; false_order.
    assert (IH1 := IHE r (refl_equal _) (make t1) (isMp_make _) z).
    assert (IH2 := IHE r (refl_equal _) (make t2) (isMp_make _) z).
    intro abs.
    destruct (eq_dec (r (make t1) (Some z)) 0); auto.
    apply IH2; intro abs'; apply abs; rewrite abs', H3; red; field; auto.
    assert (IH1 := IHE r (refl_equal _) (make t1) (isMp_make _) t).
    assert (IH2 := IHE r (refl_equal _) (make t2) (isMp_make _) t).
    apply isMp_embed.
    destruct (eq_dec (r (make t2) (Some t)) 0); auto.
    apply IH1; rewrite Huvk, H1, Qplus_0_l; assumption.
  Qed.

  Theorem make_term_of_R : forall p, 
    isZpoly p -> isMpoly p -> make (term_of_R p) === p.
  Proof.
    Lemma mk_term_of_R : forall p c p', isZpoly p -> isMpoly p ->
      mk_term c p' (term_of_R p) === addk p' c p.
    Proof.
      intros [[cp mp] wf] c p' His' HM'.
      unfold term_of_R; simpl coef_of; simpl @snd.
      assert (Hcp : isZ cp) by (exact (His' None)).
      assert (His : forall v q, MapsTo v q mp -> isZ q).
      intros. assert (R := His' (Some v)); simpl in R.
      rewrite (find_1 H) in R; assumption. clear His'.
      assert (HM : forall v q, MapsTo v q mp -> isM v).
      intros. assert (R := HM' v); simpl in R; apply R.
      generalize (@RAW.Wf_p _ _ _ wf v q H).
      rewrite (find_1 H); tauto. clear HM'.

      intro t; rewrite addk_co.
      replace (mk_poly wf t) with (RAW.coef_of (cp, mp) t) by reflexivity.
      clear wf. revert cp p' Hcp His HM t.

      pattern mp, (fold (fun v qv acc => [Qfloor qv][*]v[+]acc) mp ([0])).
      apply MapFacts.fold_rec_weak; intros.
      (* - morphism *)
      rewrite H0; auto. destruct t; simpl; try rewrite H; reflexivity.
      intros v q; rewrite H; eauto. intros v q; rewrite H; eauto.
      (* - init *)
      simpl; rewrite add_const_co; destruct t; simpl.
      rewrite MapFacts.empty_o, Qmult_0_r, Qplus_0_r; reflexivity.
      rewrite Qfloor_isZ by assumption; red; ring.
      (* - add *)
      assert (He : isZ e) by (apply His with k; apply add_1; auto).
      assert (Hk : isM k) by (apply HM with e; apply add_1; auto).
      assert (Hconst : is_const (add_const (1 * (Qfloor e # 1)) R0) === Some e).
      rewrite Qfloor_isZ by assumption; apply is_const_const.
      assert (Hconstk := isM_not_is_const k Hk).
      simpl.
      destruct (is_const (add_const (1 * (Qfloor e # 1)) R0)); 
        inversion Hconst; subst.
      unfold make in Hconstk; rewrite Hconstk.
      rewrite mk_term_make. 
      rewrite Qfloor_isZ by assumption.
      rewrite 2addk_co, add_const_co; fold (make k).
      assert (IH : mk_term c p' ([Qfloor cp][+]a) t === 
        p' t + c * RAW.coef_of (cp, m) t).
      apply H0; auto. intros; apply His with v; apply add_2; auto.
      intro abs; apply H; rewrite abs; exists q0; assumption.
      intros; apply HM with q0; apply add_2; auto.
      intro abs; apply H; rewrite abs; exists q0; assumption.
      simpl in IH; rewrite mk_term_make in IH.
      rewrite Qfloor_isZ in IH by assumption.
      rewrite addk_co, add_const_co in IH.
      rewrite Qplus_comm, Qplus_assoc; rewrite Qplus_comm in IH.
      rewrite IH; clear IH. rewrite (isM_make_embed k Hk), embed_co.
      destruct t.
      destruct (eq_dec (Some t) (Some k)).
      inversion H1; subst. simpl; rewrite MapFacts.add_eq_o by auto.
      rewrite H5. rewrite MapFacts.not_find_in_iff in H; rewrite H. 
      rewrite H3; red; ring.
      simpl; rewrite MapFacts.add_neq_o. red; ring.
      intro abs; apply H1; constructor; auto.
      destruct (eq_dec None (Some k)). inversion H1. simpl; red; ring.
    Qed.
    intros; unfold make; rewrite mk_term_of_R by assumption. 
    intro z; rewrite addk_co, P0_co; red; ring.
  Qed.
      
  Theorem find_multiple_poly : forall (P : R), isMpoly P ->
    exists m : Z, m =/= 0%Z /\ isZpoly (mult (m # 1) P) /\
      exists mP : term, make mP === mult (m # 1) P.
  Proof.
    intros P HP; exists (common_denom P).
    assert (Hp := common_denom_isZp P).
    repeat split.
    apply common_denom_nonzero.
    exact Hp.
    exists (term_of_R (mult (common_denom P # 1) P)).
    apply make_term_of_R.
    isZ. apply isMp_mult; exact HP.
  Qed.

  (** Before we can prove [implyX_entails], the last lemma we need
     is about the idempotency of substitutions. What we need in
     practice is that all the monoms in [f p], where [f = iter E] is
     an iterated substitution, are invariant by [f]. This ensures that
     the substitution we get at some point is invariant by the 
     substitution constructed up to that point. *)
  Lemma subst_idem_1 : forall (r : R) t P, r (Some t) === 0 -> 
    subst (embed t) P r === r.
  Proof.
    intros; rewrite subst_as_addk, sub_as_addk.
    intro z; rewrite !addk_co, !embed_co.
    destruct z.
    destruct (eq_dec (Some t0) (Some t)).
    inversion H0; subst. rewrite H3, H in *. red; ring.
    rewrite H; red; ring.
    destruct (eq_dec None (Some t)). inversion H0.
    rewrite H. red; ring.
  Qed.
  Lemma subst_idem_2 : forall r t (P : R), 
    P (Some t) === 0 -> subst (embed t) P r (Some t) === 0.
  Proof.
    intros; rewrite subst_as_addk, sub_as_addk, !addk_co, embed_co.
    rewrite H. destruct (eq_dec (Some t) (Some t)); [|false_order].
    red; ring.
  Qed.
  Corollary subst_idem : forall r t (P : R), P (Some t) === 0 ->
    subst (embed t) P (subst (embed t) P r) === subst (embed t) P r.
  Proof.
    intros; apply subst_idem_1; apply subst_idem_2; assumption.
  Qed.

  Lemma iter_idem_2 : forall E f, 
    Theory.iter E (Th:=Arith_theory) = Some f ->
    forall t, f (embed t) =/= embed t -> forall r, (f r) (Some t) === 0.
  Proof.
    induction E; intros f HE; simpl in HE; intros.
    contradiction H; inversion HE; reflexivity.
    destruct a as [t1 t2]; destruct (Theory.iter E) as [fE|]_eqn:HfE.
    2:discriminate.
    destruct (solve_basic_dec (fE (make t1)) (fE (make t2))).
    inversion HE; auto.
    discriminate.
    inversion HE; subst; clear HE.
    assert (IH := IHE fE (refl_equal _)); clear IHE.
    destruct (eq_dec (fE (embed t)) (embed t)).
    (* t was not substituted up to this step *)
    rewrite H0 in H.
    cut (t === t0); [intro Heq|].
    rewrite <- Heq; apply subst_idem_2.
    rewrite Hsubst. destruct (eq_dec (Some t0) (Some t)); auto.
    contradiction H1; constructor; auto.
    destruct (eq_dec t t0); auto.
    contradiction H; apply subst_idem_1; rewrite embed_co.
    destruct (eq_dec (Some t0) (Some t)); auto.
    inversion H2; subst; false_order.
    (* t was substituted before *)
    assert (IH' := IH t H0); clear IH.
    cut (P (Some t) === 0); [intro HP |].
    rewrite subst_as_addk, sub_as_addk, !addk_co, embed_co.
    destruct (eq_dec (Some t) (Some t0)).
    inversion H1; subst. rewrite <- H1, IH'; red; ring.
    rewrite IH', HP; red; ring.
    rewrite Hsubst. destruct (eq_dec (Some t0) (Some t)); auto.
    rewrite 2IH'; red; field; auto.
  Qed.
  Corollary iter_idem_2' : forall E f, 
    Theory.iter E (Th:=Arith_theory) = Some f ->
    forall t r, (f r) (Some t) =/= 0 -> f (embed t) === embed t.
  Proof.
    intros; destruct (eq_dec (f (embed t)) (embed t)); auto.
    contradiction H0; exact (iter_idem_2 E f H t H1 r).
  Qed.

  Corollary iter_idem : forall E f, 
    Theory.iter E (Th:=Arith_theory) = Some f -> forall r, f (f r) === f r.
  Proof.
    induction E; intros f HE; simpl in HE; intros.
    inversion HE; reflexivity.
    destruct a as [t1 t2]; destruct (Theory.iter E) as [fE|]_eqn:HfE.
    2:discriminate.
    destruct (solve_basic_dec (fE (make t1)) (fE (make t2))).
    inversion HE; auto.
    discriminate.
    inversion HE; subst; clear HE.
    assert (IH := IHE fE (refl_equal _)); clear IHE.
    assert (Hfm := iter_m E); rewrite HfE in Hfm.
    assert (Hlin := iter_linear E fE HfE).
    assert (Ht : fE (embed t) === embed t).
    destruct (eq_dec (fE (make t2) (Some t)) 0).
    apply (iter_idem_2' E fE HfE t (make t1)).
    rewrite Huvk, H, Qplus_0_l; exact Hk.
    exact (iter_idem_2' E fE HfE t (make t2) H).
    assert (HP : P === add (mult (1 / k)
      (sub (fE (make t2)) (fE (make t1)))) (embed t)).
    intro z; rewrite Hsubst, add_co, mult_co, sub_co, embed_co.
    destruct (eq_dec (Some t) z); destruct (eq_dec z (Some t)).
    rewrite H0, Huvk; red; field; auto.
    contradiction H0; auto. contradiction H; auto.
    red; field; auto.
    assert (HP' : fE P === P).
    rewrite HP, (iter_add E fE HfE), (iter_mult E fE HfE), 
      (iter_sub E fE HfE), Ht, 2IH; reflexivity.
    rewrite subst_idem_1.
    rewrite subst_as_addk, sub_as_addk, !Hlin.
    rewrite !IH, Ht, HP'; reflexivity.
    rewrite subst_as_addk, sub_as_addk, !Hlin.
    rewrite !IH, Ht, HP', !addk_co, !embed_co, Hsubst.
    destruct (eq_dec (Some t) (Some t)). red; ring.
    rewrite Huvk; red; field; auto.
  Qed.
  
  (** Finally, [implyX_entails] *)
  Theorem implyX_entails : 
    forall (E : list (term * term)) (u v : term),
      implyX (Th:=Arith_theory) E (make u) (make v) -> 
      models_list M E -> M |= u = v.
  Proof.
    induction E; intros u v Himp HM; unfold implyX in Himp; simpl in Himp.
    apply make_entails; assumption.
    destruct a as [a b]; unfold implyX in IHE.
    inversion HM; subst.
    destruct (Theory.iter E) as [f|]_eqn:Hf; auto.
    assert (Hfm := f_m E f Hf).
    assert (Hflin := iter_linear E f Hf).
    assert (Hsolve := solve_dec (f (make a)) (f (make b))).
    assert (HisM := isMp_iter E f Hf).
    destruct (solve_basic_dec (f (make a)) (f (make b))).
    (* -- Solved *)
    auto.
    (* -- Unsolvable *)
    set (ra := f (make a)) in *; set (rb := f (make b)) in *.
    set (q := ra None - rb None).
    assert (Hq : sub ra rb === Pq q).
    intro z; generalize (Hunsolv z); intro Hz; rewrite sub_co, Pq_co.
    destruct z. rewrite Hz; red; ring. reflexivity.
    assert (Hq0 : q =/= 0).
    intro abs; apply (Hunsolv None).
    rewrite <- (Qplus_0_r (rb None)), <- abs; unfold q; red; ring.
    clearbody q. set (c := Qnum q); set (m := Zpos (Qden q)).
    set (u' := [c]); set (v' := [m][*](a [-] b)).
    assert (Huv' : f (make u') === f (make v')).
    unfold u', v'; rewrite make_z, make_tmult_1, make_tminus.
    rewrite iter_Pz, iter_mult, iter_sub by eauto; fold ra; fold rb.
    rewrite Hq; intro z; rewrite Pz_co, mult_co, Pq_co; destruct z; auto.
    unfold c, m; apply Zify_Q.
    assert (IH := IHE u' v' Huv' H3).
    assert (Hc : c =/= 0%Z).
    intro abs; apply Hq0.
    unfold c in abs; destruct q; simpl in abs; rewrite abs; red; reflexivity.
    assert (Habs : M |= [c] <> [0]) by (rewrite models_neq_cst_iff; auto).
    contradiction Habs; change (M |= [c] = [0]).
    transitivity v'. exact IH.
    transitivity ([m] [*] (b [-] b)); [| mring].
    apply models_eq_congr; do 2 constructor; auto; [|constructor].
    apply models_eq_congr; repeat (constructor; auto).
    (* -- Subst *)
    set (ra := f (make a)) in *; set (rb := f (make b)) in *.
    destruct (find_multiple_poly P) as [m [Hm0 [Hm [mP HmP]]]].
    intro z; rewrite (Hsubst (Some z)).
    destruct (eq_dec (Some t) (Some z)).
    intro abs; false_order. unfold ra, rb.
    assert (IH1 :=  HisM (make a) (isMp_make _) z).
    assert (IH2 :=  HisM (make b) (isMp_make _) z).
    intro abs.
    destruct (eq_dec (f (make a) (Some z)) 0); auto.
    apply IH2; intro abs'; apply abs; rewrite abs', H0; red; field; auto.
    assert (HP : P === add (mult (1 / k) (sub rb ra)) (embed t)).
    intro z; rewrite Hsubst, add_co, mult_co, sub_co, embed_co.
    destruct (eq_dec (Some t) z); destruct (eq_dec z (Some t)).
    rewrite H0, Huvk. red; field; auto.
    contradiction H0; auto. contradiction H; auto.
    red; field; auto.
    clear Hsubst; inversion_clear Hsolve; clear Hnot_eq Hidem.
    simpl in Hsubst; rewrite 2subst_as_addk in Hsubst.

    set (p := embed t) in *; 
      set (rap := ra (Some t)) in *; set (rbp := rb (Some t)) in *.
    set (ka := Zpos (Qden rap)); set (kb := Zpos (Qden rbp)).
    set (la := (Qnum rap * kb)%Z); set (lb := (Qnum rbp * ka)%Z).
    set (m' := (m * ka * kb)%Z).
    set (u' := [m'][*]a [+] [la][*](mP [-] [m][*]t)).
    set (v' := [m'][*]b [+] [lb][*](mP [-] [m][*]t)).
    assert (Hfp : f p === p).
    unfold p; destruct (eq_dec rbp 0).
    apply (iter_idem_2' E f Hf t (make a)).
    fold ra; fold rap; rewrite Huvk, H, Qplus_0_l; exact Hk.
    apply (iter_idem_2' E f Hf t (make b) H).
    assert (HfP : f P === P).
    rewrite HP, (iter_add E f Hf), (iter_mult E f Hf), 
      (iter_sub E f Hf), Hfp.
    unfold ra, rb; rewrite !(iter_idem E f Hf); reflexivity.
    assert (Ht : make t === embed t).
    apply isM_make_embed.
    assert (IH1 := HisM (make a) (isMp_make _) t).
    assert (IH2 := HisM (make b) (isMp_make _) t).
    destruct (eq_dec (f (make b) (Some t)) 0); auto.
    apply IH1. fold ra; fold rap. rewrite Huvk. 
    unfold rbp, rb; rewrite H, Qplus_0_l; assumption.
    assert (Huv' : f (make u') === f (make v')).
    unfold u', v'.
    rewrite 2make_tplus, 4make_tmult_1, make_tminus, make_tmult_1.
    rewrite 2(iter_add E f), 4(iter_mult E f), 
      (iter_sub E f), (iter_mult E f) by auto.
    rewrite HmP, Ht; fold ra; fold rb; fold p.
    rewrite (iter_mult E f) by auto; rewrite HfP, Hfp.
    transitivity (mult (m' # 1) (addk ra rap (sub P p))).
    intro z.
    rewrite !add_co, !mult_co, !addk_co, !sub_co, !mult_co.
    setoid_replace (la # 1) with ((m' # 1) * rap / (m # 1)).
    red; field. intro abs; apply Hm0; destruct m; auto; discriminate abs.
    unfold la, m', ka. apply Q_cancel; auto.
    transitivity (mult (m' # 1) (addk rb rbp (sub P p))).
    rewrite Hsubst; reflexivity.
    intro z.
    rewrite !add_co, !mult_co, !addk_co, !sub_co, !mult_co.
    setoid_replace (lb # 1) with ((m' # 1) * rbp / (m # 1)).
    red; field. intro abs; apply Hm0; destruct m; auto; discriminate abs.
    unfold lb, m', kb.
    replace (m * ka * Zpos (Qden rbp))%Z 
      with (m * Zpos (Qden rbp) * ka)%Z by ring.
    apply Q_cancel; auto.
    assert (IH := IHE u' v' Huv' H3).
    assert (HpP : M |= mP [-] [m][*]t = [0]).
    apply models_integral with (la - lb)%Z.
    transitivity  ([0]); [|mring].
    rewrite push_minus, push_tminus_tmult; symmetry; rewrite <- push_right_eq.
    transitivity (u' [-] [m'][*]a); [unfold u'; mring |].
    transitivity (v' [-] [m'][*]b); [| unfold v'; mring].
    apply models_eq_congr; do 2 (constructor; auto); [|constructor].
    apply models_eq_congr; do 3 (constructor; auto).
    intro abs; apply Zminus_eq in abs; revert abs.
(*     intro abs; change (M |= [la] [-] [lb] = [0]) in abs. *)
(*     symmetry in abs; rewrite <- push_right_eq, models_eq_cst_iff in abs. *)
    (* revert abs *) 
    unfold la, lb, ka, kb; refine (Q_neq _ _ _).
    rewrite Huvk. intro abs; apply Hk.
    transitivity (rbp - rbp); [ rewrite <- abs at 1|]; red; ring.
    clear u' v' IH Huv' m' la lb ka kb Hsubst.

    unfold p in Himp; rewrite 2subst_as_addk in Himp; fold p in Himp.
    set (fu := f (make u)) in *; set (fv := f (make v)) in *.
    set (fup := fu (Some t)) in *; set (fvp := fv (Some t)) in *.
    set (ku := Zpos (Qden fup)); set (kv := Zpos (Qden fvp)).
    set (lu := (Qnum fup * kv)%Z); set (lv := (Qnum fvp * ku)%Z).
    set (K := (m * ku * kv)%Z).
    set (u' := [K][*]u [+] [lu][*](mP [-] [m][*]t)).
    set (v' := [K][*]v [+] [lv][*](mP [-] [m][*]t)).
    assert (Huv' : f (make u') === f (make v')).
    unfold u', v'.
    rewrite 2make_tplus, 4make_tmult_1, make_tminus, make_tmult_1.
    rewrite 2(iter_add E f), 4(iter_mult E f), 
      (iter_sub E f), (iter_mult E f) by auto.
    rewrite HmP, Ht; fold p; fold fu; fold fv.
    rewrite (iter_mult E f) by auto; rewrite HfP, Hfp.
    transitivity (mult (K # 1) (addk fu fup (sub P p))).
    intro z.
    rewrite !add_co, !mult_co, !addk_co, !sub_co, !mult_co.
    setoid_replace (lu # 1) with ((K # 1) * fup / (m # 1)).
    red; field. intro abs; apply Hm0; destruct m; auto; discriminate abs.
    unfold lu, K, kv. apply Q_cancel; auto.
    transitivity (mult (K # 1) (addk fv fvp (sub P p))).
    rewrite Himp; reflexivity.
    intro z.
    rewrite !add_co, !mult_co, !addk_co, !sub_co, !mult_co.
    setoid_replace (lv # 1) with ((K # 1) * fvp / (m # 1)).
    red; field. intro abs; apply Hm0; destruct m; auto; discriminate abs.
    unfold lv, K, kv.
    replace (m * ku * Zpos (Qden fvp))%Z 
      with (m * Zpos (Qden fvp) * ku)%Z by ring.
    apply Q_cancel; auto.
    assert (IH := IHE u' v' Huv' H3).
    apply models_integral with K.
    transitivity u'; [| transitivity v'; [exact IH|]].
    unfold u'; apply tplus_0_equal; apply tmult_0_equal; exact HpP.
    unfold v'; symmetry; apply tplus_0_equal; apply tmult_0_equal; exact HpP.
    unfold K; intro HK.
    destruct (Zmult_integral _ _ HK).
    destruct (Zmult_integral _ _ H). auto.
    discriminate H0. discriminate H.
  Qed.
End ZEntailment.
  
(* Prerequisites for ZEntailment : (integral commutative) ring laws must
   hold in all term models. *)
Module ModelsAsRing.
  Import SemLazy.SEMLAZY.
  Open Scope sem_scope.

  Theorem implyX_entails : 
    forall (E : list (term * term)) (u v : term),
      implyX (Th:=Arith_theory) E (make u) (make v) -> E |- u = v.
  Proof.
    repeat intro.
    refine (implyX_entails M _ _ E u v H H0).
    constructor; intros; unfold models_eq, model_as_fun, 
      LLazy.LLAZY.interp, LLazy.LLAZY.RAW.interp; simpl;
        try (apply ModelsRingExt.mext_rule; constructor; auto);
      apply ModelsRingExt.mext_sym; 
        apply ModelsRingExt.mext_rule; constructor; auto.
    exact (ModelsRingExt.eq_integral M).
  Qed.
End ModelsAsRing.

Module ArithTheory.
  Definition Th := Arith_theory.
  Existing Instance Th.
  
  Theorem ThSpecs : TheorySpecs Th.
  Proof. constructor.
    exact subst_m.
    exact leaves_m.
    exact solve_m.
    exact leaves_not_empty.
    exact implyX_specs.
    exact ModelsAsRing.implyX_entails.
    exact solve_dec.
  Qed.
  Existing Instance ThSpecs.
End ArithTheory.
