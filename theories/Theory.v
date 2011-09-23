Require Import Containers.OrderedType TermUtils SetoidList.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Inductive Solution (R : Type) : Type :=
| Solved
| Unsolvable
| Subst (p : R) (P : R).

Section Solution_OT.
  Context `{R_OT : OrderedType R}.

  Inductive solution_eq : Solution R -> Solution R -> Prop :=
  | solution_eq_Solved : solution_eq (Solved R) (Solved R)
  | solution_eq_Unsolvable : solution_eq (Unsolvable R) (Unsolvable R)
  | solution_eq_Subst :
    forall p p' P P', p === p' -> P === P' -> 
      solution_eq (Subst p P) (Subst p' P').

  Property solution_eq_refl : Reflexive solution_eq.
  Proof. Tactics.inductive_refl. Qed.
  Property solution_eq_sym : Symmetric solution_eq.
  Proof. Tactics.inductive_sym. Qed.
  Property solution_eq_trans : Transitive solution_eq.
  Proof. Tactics.inductive_trans. Qed.

  Global Instance solution_eq_Equiv : Equivalence solution_eq := {
    Equivalence_Reflexive := solution_eq_refl;
    Equivalence_Symmetric := solution_eq_sym;
    Equivalence_Transitive := solution_eq_trans
  }.
End Solution_OT.

(** * Theory *)
Class Theory := {
  (** An (ordered) type of semantical values *)
  R : Type;
  R_OT :> OrderedType R;
  (** Operations *)
  make : term -> R;
  one : R;
  leaves : R -> list R;
  subst : R -> R -> R -> R;
  solve : R -> R -> Solution R
}.

(** * TheorySpecs *)
Require Import SemLazy.
Import SEMLAZY.
Section TheorySpecs.
  Context `{Th: Theory}.

  (** Equality entailment on the semantic level can be described
     through the following [iter] function. [iter] expresses the
     step-by-step iteration of a subst/solve cycle on a list
     of equations between terms. *)
  Fixpoint iter (E : list (term * term)) : option (R -> R) :=
    match E with
      | nil => Some (fun r => r)
      | (t1, t2)::E' =>
        match iter E' with
          | Some i =>
            let r1 := i (make t1) in
            let r2 := i (make t2) in
              match solve r1 r2 with
                | Solved => Some i
                | Unsolvable => None
                | Subst p P => Some (fun r => subst p P (i r))
              end
          | None => None
        end
    end.
  (** An equality between two semantic values is entailed by
     a set of term equalities if their iterations are equal.
     We use [solve] to test the equalities, because [solve]
     can be more complete than [===]. *)
  Definition implyX (E : list (term * term)) (r1 r2 : R) :=
    match iter E with
      | Some uf => uf r1 === uf r2
      | None => True
    end.

  (** [equivX] shall be an equivalence relation, but this will be
     a consequence of the properties of [solve]; as for [implyX], it should
     also include equations that are on the left-hand side and be
     monotonic with respect to these equations, as well as consistent with
     subst and solve. *)
  Class implyX_Specs := {
    (* implyX_Ax : forall l t u, In (t, u) l -> implyX l (make t) (make u); *)
    (* implyX_weaken : forall l u v a b,  *)
    (*   implyX l a b -> implyX ((u, v)::l) a b; *)
    implyX_Subst : forall l a b p P,
      implyX l p P -> b === subst p P a -> implyX l a b;
     implyX_Solve : forall l a b u v,
       implyX l u v -> solution_eq (solve u v) (Subst a b) -> implyX l a b
  }.
    
  (* Specifications of [solve] *)
  Inductive solve_specs (u v : R) : Solution R -> Prop :=
  | solve_specs_Solved :
    forall (Hsolved : u === v), solve_specs u v (Solved R)
  | solve_specs_Unsolvable :
    forall 
      (Hnot_eq : u =/= v)
      (Hunsolv : forall l, implyX l u v -> forall a b, implyX l a b),
      solve_specs u v (Unsolvable R)
  | solve_specs_Subst :
    forall p P 
      (Hnot_eq : u =/= v)
      (Hsubst : subst p P u === subst p P v)
      (Hidem : ~ InA _eq p (leaves P)),
      solve_specs u v (Subst p P).
      
  Class TheorySpecs := {
    (* - Morphisms *)
    subst_m :> Proper (_eq ==> _eq ==> _eq ==> _eq) subst;
    leaves_m :> Proper (_eq ==> _eq) leaves;
    solve_m :> Proper (_eq ==> _eq ==> 
      @Equivalence.equiv _ _ (solution_eq_Equiv)) solve;
    (* - [leaves] is never empty *)
    leaves_not_empty : 
      forall r, leaves r <> nil;
    (* - implication in [R] and its properties semantic entailment *)
    implyX_dec :> implyX_Specs;
    implyX_entails :
      forall E u v, implyX E (make u) (make v) -> E |- u = v;
    (* - interaction of [solve] and [subst] *)
    solve_dec : 
      forall u v, solve_specs u v (solve u v)
  }.
End TheorySpecs.
Implicit Arguments TheorySpecs [].

Section WithTheorySpecs.
  Context `{ThSpecs: @TheorySpecs Th}.

  Theorem iter_m : forall E, 
    match iter E with
      | Some f => Proper (_eq ==> _eq) f
      | None => True
    end.
  Proof.
    induction E; simpl.
    repeat intro; auto.
    destruct a as [t1 t2]; destruct (iter E) as [f|]; auto.
    destruct (solve (f (make t1)) (f (make t2))); auto.
    repeat intro; rewrite H; auto.
  Qed.
  Global Instance implyX_m (E : list (term * term)) :
    Proper (_eq ==> _eq ==> iff) (implyX E).
  Proof.
    intros; repeat intro; unfold implyX.
    assert (Hm := iter_m E); destruct (iter E) as [f|].
    rewrite H, H0; reflexivity.
    reflexivity.
  Qed.

  Global Instance implyX_Refl E : Reflexive (implyX E).
  Proof.
    repeat intro; unfold implyX; destruct (iter E); auto.
  Qed.
  Global Instance implyX_Sym E : Symmetric (implyX E).
  Proof.
    repeat intro; unfold implyX in *; destruct (iter E); auto.
  Qed.
  Global Instance implyX_Trans E : Transitive (implyX E).
  Proof.
    repeat intro; unfold implyX in *; destruct (iter E); order.
  Qed.

  Remark implyX_impl : 
    forall l a b, implyX l a b -> 
      forall a' b', a === a' -> b === b' -> implyX l a' b'.
  Proof.
    intros; rewrite <- H0, <- H1; assumption.
  Qed.

  Property make_sound :
    forall t u, make t === make u -> forall M, M |= t = u.
  Proof.
    intros.
    refine (implyX_entails (E:=nil) _ _).
    rewrite H; reflexivity.
    constructor.
  Qed.
  Property solve_trivial : 
    forall u v, u === v <-> solve u v = Solved R.
  Proof.
    intros u v; destruct (solve_dec u v).
    split; intro; auto.
    split; intro; try discriminate; order.
    split; intro; try discriminate; order.
  Qed.

  Property implyX_Ax :
    forall E t u, In (t, u) E -> implyX E (make t) (make u).
  Proof.
    induction E; intros; unfold implyX; simpl; inversion H.
    subst.
    assert (Hm := iter_m E); destruct (iter E) as [f|]; auto.
    destruct (solve_dec (f (make t)) (f (make u))); auto.
    clear H; assert (IH := IHE t u H0); clear H0 IHE; unfold implyX in IH.
    destruct a as [t1 t2]; assert (Hm := iter_m E); destruct (iter E) as [f|].
    destruct (solve_dec (f (make t1)) (f (make t2))); auto.
    rewrite IH; reflexivity. trivial.
  Qed.
  Property implyX_weaken : forall E u v a b,
    implyX E a b -> implyX ((u, v)::E) a b.
  Proof.
    induction E; intros; unfold implyX in *; simpl in *.
    destruct (solve_dec (make u) (make v)); try rewrite H; auto.
    destruct a as [t1 t2]; assert (Hm := iter_m E); destruct (iter E) as [f|].
    2:auto.
    destruct (solve_dec (f (make t1)) (f (make t2))); auto.
    apply IHE; auto.
    destruct (solve_dec (subst p P (f (make u)))
      (subst p P (f (make v)))); auto.
    rewrite H; reflexivity.
  Qed.
(*   Property implyX_Subst_direct : forall E a b p P, *)
(*     implyX E p P -> b === subst p P a -> implyX E a b. *)
(*   Proof. *)
(*     induction E; intros; unfold implyX in *; simpl in *. *)
(*     admit. (* subst r p p === r forall p r *) *)
(*     destruct a as [t1 t2]; assert (Hm := iter_m E); destruct (iter E) as [f|]. *)
(*     2:auto. *)
(*     destruct (solve_dec (f (make t1)) (f (make t2))); auto. *)
(*     exact (IHE a0 b p P H H0). *)
(*     admit. (* ?? *) *)
(*   Qed. *)
(*   Property implyX_Solve_direct : forall E a b u v, *)
(*     implyX E u v -> solution_eq (solve u v) (Subst a b) -> implyX E a b. *)
(*   Proof. *)
(*     induction E; intros; unfold implyX in *; simpl in *. *)
(*     destruct (solve_dec u v); inversion_clear H0. *)
(*     contradiction (Hnot_eq H). *)
(*     destruct a as [t1 t2]; assert (Hm := iter_m E); destruct (iter E) as [f|]. *)
(*     2:auto. *)
(*     destruct (solve_dec (f (make t1)) (f (make t2))); auto. *)
(*     eauto. *)
(*     assert (IH := IHE a0 b u v). *)
(*     destruct (solve_dec u v); inversion_clear H0. *)
(*     (* et si E |= iter(E,r) = r ? *) *)
(*     admit. (* ?? *) *)
(*   Qed. *) 
End WithTheorySpecs.
  
(** * Example *)
Module EmptyTheory.
  Local Instance Empty_theory : Theory := {
    R := term;
    R_OT := term_OT;
    make := fun t => t;
    one := Term.app (Op DomainNat Plus) Term.tnil; (* bottom == +() *)
    leaves := fun t => t::nil;
    subst := fun p P r => if p == r then P else r;
    solve := fun r1 r2 => if r1 == r2 then Solved _ else Subst r1 r2
  }.
  Definition Th := Empty_theory.
  Existing Instance Th.

  Corollary implyX_m : forall l u v, u === v -> implyX l u v.
  Proof.
    induction l; intros; unfold implyX in *; simpl in *.
    assumption.
    destruct a; destruct (iter l) as [f|]; auto.
    destruct (eq_dec (f t : term) (f t0)).
    auto.
    destruct (eq_dec (f t : term) (f u));
      destruct (eq_dec (f t : term) (f v)).
    reflexivity. congruence. congruence. auto.
  Qed.
   
  Local Instance Empty_theory_implyX : @implyX_Specs Empty_theory.
  Proof. constructor; intros.
    (* - Subst *)
    unfold implyX in *; simpl in *; destruct (iter l); auto.
    destruct (eq_dec p a).
    rewrite H1 in H; rewrite <- H0 in H; assumption.
    rewrite H0; reflexivity.
    (* - Solve *)
    unfold implyX in *; destruct (iter l); auto.
    simpl in H0; destruct (eq_dec (u : term) v); inversion H0; subst.
    rewrite H5, H7 in H; assumption.
  Qed.

  Local Instance Empty_theory_specs : TheorySpecs Empty_theory.
  Proof. constructor.
    (* - morphisms *)
    repeat intro; congruence.
    repeat intro; simpl; constructor (auto; constructor).
    repeat intro; simpl; rewrite H, H0.
    destruct (@eq_dec _ term_OT y y0); auto.
    rewrite H, H0; reflexivity.
    (* - leaves_not_empty *)
    intro; compute; discriminate.
    (* - implyX_specs *)
    exact Empty_theory_implyX.
    (* - implyX_entails *)
    induction E; intros u v H M HM.
    unfold implyX in H; simpl in H.
    rewrite H; apply models_eq_refl.
    destruct a as [a b]; inversion HM; subst; clear HM.
    unfold implyX in *; simpl in *.
    destruct (iter E) as [f|].
    destruct (eq_dec (f a : term) (f b)).
    exact (IHE u v H M H4).
    destruct (eq_dec (f a : term) (f u));
      destruct (eq_dec (f a : term) (f v)).
    refine (IHE u v _ M H4); order.
    generalize (IHE _ _ H M H4) (IHE _ _ H1 M H4); intros.
    eauto using models_eq_sym, models_eq_trans.
    generalize (IHE _ _ H M H4) (IHE _ _ H3 M H4); intros.
    eauto using models_eq_sym, models_eq_trans.
    refine (IHE u v _ M H4); auto.
    exact (IHE u v I M H4).
    (* - solve_specs *)
    intros u v; unfold solve; simpl.
    destruct (eq_dec (u : term) v) as [Heq|Hneq]; constructor.
    rewrite Heq; reflexivity.
    auto.
    simpl; destruct (eq_dec (u : term) u); try order.
    destruct (eq_dec (u : term) v); auto.
    simpl; intro abs; inversion_clear abs; auto; inversion H.
  Qed.
  Definition ThSpecs := Empty_theory_specs.
  Existing Instance ThSpecs.
End EmptyTheory.