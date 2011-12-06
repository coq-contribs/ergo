Require Import Quote List Ergo Term TermUtils.
Require Import Containers.OrderedType Nfix.

Generalizable All Variables.

Definition typeZ := typeArith DomainZ.
Definition tplus t u :=
  app (Op DomainZ Plus) (tcons t (tcons u tnil)).
Definition tmult t u :=
  app (Op DomainZ Mult) (tcons t (tcons u tnil)).
Definition tminus t u :=
  app (Op DomainZ Minus) (tcons t (tcons u tnil)).
Definition topp t :=
  app (Op DomainZ Opp) (tcons t tnil).
Definition tdiv t u :=
  app (Op DomainZ Div) (tcons t (tcons u tnil)).

Notation "t [+] u" := (tplus t u)(at level 24).
Notation "t [-] u" := (tminus t u)(at level 23).
Notation "t [*] u" := (tmult t u)(at level 22).
Notation "t [/] u" := (tdiv t u)(at level 21).
Notation "[ z ]" := (app (Cst DomainZ (z%Z)) tnil).

Inductive ZRing : term -> term -> Prop :=
| ZRing_add_0_l : 
  forall u, ZRing u ([0] [+] u) (* wt *)
| ZRing_add_comm : 
  forall u v, ZRing (u [+] v) (v [+] u)
| ZRing_add_assoc : 
  forall u v w, ZRing (u [+] (v [+] w)) ((u [+] v) [+] w)
| ZRing_mul_1_l : 
  forall u, ZRing u ([1] [*] u) (* wt *)
| ZRing_mul_comm : 
  forall u v, ZRing (u [*] v) (v [*] u)
| ZRing_mul_assoc : 
  forall u v w, ZRing (u [*] (v [*] w)) ((u [*] v) [*] w)
| ZRing_distr_l : 
  forall u v w, ZRing ((u [+] v) [*] w) ((u [*] w) [+] (v [*] w))
| ZRing_sub_def : 
  forall u v, ZRing (u [-] v) (u [+] (topp v))
| ZRing_opp_def : 
  forall u, ZRing [0] (u [+] topp u) (* wt *)
    (* a bit more than a ring, we add a thing about euclidean division
       in order to obtain that it is also an integral ring. It is an
       intricate way to state that but the other intuitive ways raise issues :
       - u * v = 0 -> u = 0 \/ v = 0 ends up in a disjunction which is no good
       - k * u = k * v -> u * v requires ZRing to be mutually inductive
       with mext
       *)
| ZRing_div_cancel : 
  forall k u, k =/= 0%Z -> ZRing u (([k] [*] u) [/] [k]).  (* wt *)

(* (* I-substitutions *) *)
(* Definition isubst := list (term * term). *)
(* Fixpoint assoc (t : term) (s : isubst) := *)
(*   match s with *)
(*     | nil => None *)
(*     | (p, P)::q =>  *)
(*       if p == t then Some P else assoc t q *)
(*   end. *)

(* Nested Fixpoint subst (t : term) (s : isubst) : term := *)
(*   match assoc t s with *)
(*     | Some P => P *)
(*     | None => *)
(*       match t with *)
(*         | app f l => app f (subst_terms l s) *)
(*       end *)
(*   end *)
(* with subst_terms (lt : terms) (s : isubst) : terms := *)
(*   match lt with *)
(*     | nil => nil *)
(*     | cons t q => (subst t s)::(subst_terms q s) *)
(*   end. *)

(* Property subst_1 : forall t, subst t nil = t. *)
(* Proof. *)
(*   induction t using term_terms_rect_default; simpl. *)
(*   f_equal; induction lt; simpl; auto. *)
(*   rewrite IHlt, H; intuition. *)
(* Qed. *)
(* Property subst_2 : forall s t p, assoc t s = Some p -> subst t s = p.  *)
(* Proof. *)
(*   intros; destruct t; simpl. *)
(*   rewrite H; reflexivity. *)
(* Qed. *)
(* Definition none_integer (s : isubst) (M : varmaps) := *)
(*   forall p, In p s ->  *)
(*     ~ well_typed (varmaps_vty M) (varmaps_vsy M) (fst p) typeZ. *)

(* Property assoc_in_1 :   *)
(*   forall s t P, assoc t s = Some P -> In (t, P) s. *)
(* Proof. *)
(*   induction s; intros; simpl in *. *)
(*   discriminate. *)
(*   destruct a as [p P']; destruct (eq_dec p t); [left | right]. *)
(*   inversion H; subst; rewrite H0; reflexivity. *)
(*   intuition. *)
(* Qed. *)

(* (* Property wt_subst_1 :  *) *)
(* (*   forall M t s,  *) *)
(* (*     all_ill_typed s M -> *) *)
(* (*     has_type (varmaps_vty M) (varmaps_vsy M) t  *) *)
(* (*     (type_of (varmaps_vty M) (varmaps_vsy M) t) = true -> *) *)
(* (*     subst t s = t. *) *)
(* (* Proof. *) *)
(* (*   intro M; induction t using term_terms_rect_default; intros. *) *)
(* (*   simpl; destruct (assoc (app f lt) s) as [ ]_eqn:Hassoc. *) *)
(* (*   assert (R := H0 (app f lt, t) (assoc_in_1 _ _ _ Hassoc)). *) *)
(* (*   simpl fst in R; congruence. *) *)
(* (*   f_equal; clear Hassoc. *) *)
(* (*   apply has_type_1 in H1. *) *)
(* (*   inversion_clear H1; revert H2. *) *)
(* (*   generalize (type_of (varmaps_vty M) (varmaps_vsy M) (app f lt));  *) *)
(* (*     generalize (lookup_type (varmaps_vty M) (varmaps_vsy M) f); intros. *) *)
(* (*   revert t t0 H2; induction lt; intros; simpl. *) *)
(* (*   reflexivity. *) *)
(* (*   inversion_clear H2; f_equal. *) *)
(* (*   apply H; intuition. apply has_type_2 in H3. *) *)
(* (*   rewrite <- (has_type_is_type_of _ _ _ _ H3); exact H3. *) *)
(* (*   apply IHlt with t3 t0; intuition. *) *)
(* (* Qed. *) *)

(* Definition is_integer M t := *)
(*   well_typed (varmaps_vty M) (varmaps_vsy M) t typeZ. *)
(* Property is_integer_cst : forall M k, is_integer M [k]. *)
(* Proof. *)
(*   constructor; simpl; constructor. *)
(* Qed. *)
(* Property is_integer_tplus : forall M t u,  *)
(*   is_integer M t -> is_integer M u -> is_integer M (t [+] u). *)
(* Proof. *)
(*   intros; constructor; simpl; repeat constructor; assumption. *)
(* Qed. *)
(* Property is_integer_tminus : forall M t u,  *)
(*   is_integer M t -> is_integer M u -> is_integer M (t [-] u). *)
(* Proof. *)
(*   intros; constructor; simpl; repeat constructor; assumption. *)
(* Qed. *)
(* Property is_integer_tmult : forall M t u,  *)
(*   is_integer M t -> is_integer M u -> is_integer M (t [*] u). *)
(* Proof. *)
(*   intros; constructor; simpl; repeat constructor; assumption. *)
(* Qed. *)
(* Property is_integer_topp : forall M t,  *)
(*   is_integer M t -> is_integer M (topp t). *)
(* Proof. *)
(*   intros; constructor; simpl; repeat constructor; assumption. *)
(* Qed. *)
(* Ltac is_integer := *)
(*   auto using is_integer_cst, is_integer_tplus, is_integer_tminus, *)
(*     is_integer_tmult, is_integer_topp. *)
(* Ltac case_integer M t := *)
(*   destruct (well_typed_dec (varmaps_vty M) (varmaps_vsy M) t typeZ). *)

(* Inductive subst_bad_eqn (M : varmaps) (t u : term) : Prop := *)
(* | subst_bad_eqn_intro : *)
(*   forall (s : isubst) (Hills : none_integer s M) *)
(*     (Hwt_t : is_integer M (subst t s)) (Hwt_u : is_integer M (subst u s)), *)
(*     ZRing (subst t s) (subst u s) -> subst_bad_eqn M t u. *)

(* Remark subst_bad_eqn_wt :  *)
(*   forall M t u, ZRing t u ->  *)
(*     is_integer M t -> is_integer M u -> subst_bad_eqn M t u. *)
(* Proof. *)
(*   intros; exists nil; auto. *)
(*   intros ? p; inversion p. *)
(*   rewrite subst_1; assumption. *)
(*   rewrite subst_1; assumption. *)
(*   rewrite 2subst_1; assumption. *)
(* Qed. *)
Hint Constructors ZRing.

Lemma is_eq_refl `{OrderedType A} : forall (x : A), x == x = true.
Proof.
  intros; destruct (eq_dec x x); auto; false_order.
Qed.
Lemma is_eq_sym `{OrderedType A} : forall (x y : A), (x == y) = (y == x).
Proof.
  intros; destruct (eq_dec x y); destruct (eq_dec y x); auto; false_order.
Qed.

(* Theorem rewrite_ZRing_wt :  *)
(*   forall M t u, ZRing t u -> subst_bad_eqn M t u. *)
(* Proof. *)
(*   intros M t u H; destruct H. *)
(*   (* - 1 *) *)
(*   case_integer M u. *)
(*   apply subst_bad_eqn_wt; auto. *)
(*   is_integer. *)
(*   pose (s := (u, [1])::nil). *)
(*   assert (Hu : subst u s = [1]). *)
(*   apply subst_2; simpl; rewrite is_eq_refl; reflexivity. *)
(*   assert (Hu0 : subst (u[+][0]) s = [1][+][0]). *)
(*   simpl; fold (u [+] [0]). *)
(*   destruct (eq_dec u (u [+] [0])). *)
(*   admit. (* occur check *) *)
(*   rewrite Hu; destruct (eq_dec u [0]). *)
(*   contradiction n; rewrite H0; apply has_type_1; reflexivity. *)
(*   reflexivity. *)
(*   exists s. *)
(*   repeat intro. inversion H; [|contradiction]. *)
(*   subst; simpl in H0; auto. *)
(*   rewrite Hu0; is_integer. rewrite Hu; is_integer. *)
(*   rewrite Hu0, Hu; auto. *)
(*   (* - 2 *) *)
(*   admit. *)
(*   (* - 3 *) *)
(*   admit. *)
(*   (* - 4 *) *)
(*   case_integer M u. *)
(*   apply subst_bad_eqn_wt; auto. *)
(*   is_integer. *)
(*   pose (s := (u, [1])::nil). *)
(*   assert (Hu : subst u s = [1]). *)
(*   apply subst_2; simpl; rewrite is_eq_refl; reflexivity. *)
(*   assert (H1u : subst ([1][*]u) s = [1][*][1]). *)
(*   simpl; fold ([1][*]u). *)
(*   destruct (eq_dec u ([1][*]u)). *)
(*   admit.  (* occur check *) *)
(*   rewrite Hu; destruct (eq_dec u [1]). *)
(*   contradiction n; rewrite H0; apply has_type_1; reflexivity. *)
(*   reflexivity. *)
(*   exists s. *)
(*   repeat intro. inversion H; [|contradiction]. *)
(*   subst; simpl in H0; auto. *)
(*   rewrite H1u; is_integer. rewrite Hu; is_integer. *)
(*   rewrite H1u, Hu; auto. *)
(*   (* - 5 *) *)
(*   admit. *)
(*   (* - 6 *) *)
(*   admit. *)
(*   (* - 7 *) *)
(*   admit. *)
(*   (* - 8 *) *)
(*   admit. *)
(*   (* - 9 *) *)
(*   case_integer M u. *)
(*   apply subst_bad_eqn_wt; auto. *)
(*   is_integer. is_integer. *)
(*   pose (s := (u, [1])::nil). *)
(*   assert (Hu : subst u s = [1]). *)
(*   apply subst_2; simpl; rewrite is_eq_refl; reflexivity. *)
(*   assert (Huu : subst (u[+]topp u) s = [1][+]topp [1]). *)
(*   simpl; fold (u [+] topp u). *)
(*   destruct (eq_dec u (u [+] topp u)). *)
(*   admit.  (* occur check *) *)
(*   fold (topp u); rewrite Hu; destruct (eq_dec u (topp u)). *)
(*   admit.  (* occur check *) *)
(*   reflexivity. *)
(*   assert (H0 : subst [0] s = [0]). *)
(*   simpl; destruct (eq_dec u [0]); auto. *)
(*   contradiction n; rewrite H; apply has_type_1; reflexivity. *)
(*   exists s. *)
(*   repeat intro. inversion H; [|contradiction]. *)
(*   subst; simpl in H0; auto. *)
(*   rewrite Huu; is_integer. rewrite H0; is_integer. *)
(*   rewrite Huu, H0; auto. *)
(* Qed. *)

(** Properties of [ZRing] with respect to typing *)
Notation "'type' 'of' t 'in' M" :=
  (type_of (varmaps_vty M) (varmaps_vsy M) t) (at level 1).
Notation "'wt' t 'in' M" := 
  (has_type (varmaps_vty M) (varmaps_vsy M) t 
    (type of t in M))(at level 1, t at level 200).
Ltac ite H :=
  match goal with
    | H : (if ?E then ?C else false) = true |- _ =>
      let Hif := fresh "if" in
        destruct E as [ ]_eqn:Hif; try discriminate H
  end.
Ltac find_type :=
  match goal with
    | H : has_type ?vty ?vsy ?t ?ty = true |- _ =>
      rewrite (has_type_is_type_of vty vsy t ty H) in *
    | _ => idtac "Nothing to do."
  end.

Property ZRing_well_type_1 : 
  forall M u v, wt u in M = true -> wt v in M = true ->
    ZRing u v -> type of u in M = typeArith DomainZ.
Proof.
  intros M u v wfu wfv H; destruct H; simpl in *; try reflexivity.
  ite wfu; find_type; reflexivity.
  ite wfu; find_type; reflexivity.
  do 2 ite wfu; find_type; reflexivity.
Qed.
Property ZRing_well_type_2 : 
  forall M u v, wt u in M = true -> wt v in M = true ->
    ZRing u v -> type of v in M = typeArith DomainZ.
Proof.
  intros M u v wfu wfv H; destruct H; simpl in *; reflexivity.
Qed.
Corollary ZRing_well_type_eq : 
  forall M u v, wt u in M = true -> wt v in M = true ->
    ZRing u v -> type of u in M = type of v in M.
Proof.
  intros; rewrite
    (ZRing_well_type_1 M u v H H0 H1), (ZRing_well_type_2 M u v H H0 H1).
  reflexivity.
Qed.

Module GenericCongrClosure.
Section WithRelation.
  Variable R : term -> term -> Prop.

  Inductive mext : term -> term -> Prop :=
  | mext_rule : forall t u, R t u -> mext t u
  | mext_refl :
    forall t, mext t t
  | mext_sym :
    forall t u, mext u t -> mext t u
  | mext_trans :
    forall t v u, mext t v -> mext v u -> mext t u
  | mext_congr :
    forall f lt lu, mext_terms lt lu -> mext (app f lt) (app f lu)
  with mext_terms : terms -> terms -> Prop :=
  | mext_nil :
    mext_terms nil nil
  | mext_cons :
    forall t u lt lu,
      mext t u -> mext_terms lt lu -> mext_terms (t::lt) (u::lu).
  Generate Scheme mext.

  Fixpoint forall2 {A B : Type} (f : A -> B -> Prop) 
    (la : list A) (lb : list B) :=
    match la, lb with
      | nil, nil => True
      | a::qa, b::qb => f a b /\ forall2 f qa qb
      | _, _ => False
    end.
  Fixpoint forall3 {A B C : Type} (f : A -> B -> C -> Prop) 
    (la : list A) (lb : list B) (lc : list C) :=
    match la, lb, lc with
      | nil, nil, nil => True
      | a::qa, b::qb, c::qc => f a b c /\ forall3 f qa qb qc
      | _, _, _ => False
    end.

  Definition Congruence (C : term -> term -> Prop) :=
    forall f lt lu, forall2 C lt lu -> C (app f lt) (app f lu).

  (** Since [mext] is the reflexive, symmetric, transitive and congruent
     closure of [R], it is contained in any congruence relation extending [R]. 
     *)
  Section Closure.
    Variable C : term -> term -> Prop.
    Variable C_refl : Reflexive C.
    Variable C_sym : Symmetric C.
    Variable C_trans : Transitive C.
    Variable C_congr : Congruence C.
    Variable C_R : forall t u, R t u -> C t u.

    Theorem smallest_closure : forall t u, mext t u -> C t u.
    Proof.
      intros; induction H using mext_mutual_ind with
        (P := fun t u H => C t u)
        (P0 := fun lt lu H => forall2 C lt lu); simpl; eauto.
    Qed.
  End Closure.

  Definition path := list nat.
  Inductive rel_at : path -> term -> term -> Prop :=
  | rel_at_here : forall t u, R t u -> rel_at nil t u
  | rel_at_next : forall n p f lt lu, rel_at_terms n p lt lu ->
    rel_at (n::p) (app f lt) (app f lu)
  with rel_at_terms : nat -> path -> terms -> terms -> Prop :=
  | rel_at_terms_0 : forall p t u l,
    rel_at p t u -> rel_at_terms O p (t::l) (u::l)
  | rel_at_terms_S : forall n p t lt lu,
    rel_at_terms n p lt lu -> rel_at_terms (S n) p (t::lt) (t::lu).
  Generate Scheme rel_at.

  Inductive rel_chain : list path -> term -> term -> Prop :=
  | rel_chain_nil : forall t, rel_chain nil t t
  | rel_chain_cons : 
    forall t v u p lp, rel_at p t v -> rel_chain lp v u ->
      rel_chain (p::lp) t u.
  Definition linked (t u : term) :=
    exists lp : list path, rel_chain lp t u.

  (** Alternative constructors for [rel_chain] *)
  Lemma rel_chain_app : forall t v u lp lp', 
    rel_chain lp t v -> rel_chain lp' v u -> rel_chain (lp ++ lp') t u.
  Proof.
    intros t v u lp; revert t v u; induction lp; intros; simpl.
    inversion_clear H; auto.
    inversion_clear H.
    constructor 2 with v0; auto; apply IHlp with v; assumption.
  Qed.
  Lemma rel_chain_singl : forall t v p,
    rel_at p t v -> rel_chain (p::nil) t v.
  Proof.
    intros; constructor 2 with v; auto; constructor.
  Qed.

  (** [linked] is a congruence relation *)
  Property linked_refl : Reflexive linked.
  Proof.
    intro t; exists nil; constructor.
  Qed.
  Variable R_sym : Symmetric R.
  Property linked_sym : Symmetric linked.
  Proof.
    intros t u [lp H]; exists (rev lp); induction H.
    constructor.
    apply rel_chain_app with v; auto.
    apply rel_chain_singl.
    Lemma rel_at_sym : forall t u p, rel_at p t u -> rel_at p u t.
    Proof.
      intros.
      induction H using rel_at_mutual_ind with
        (P := fun p t u H => rel_at p u t)
        (P0 := fun n p lt lu H => rel_at_terms n p lu lt);
        constructor (auto).
    Qed.
    apply rel_at_sym; assumption.
  Qed.
  Property linked_trans : Transitive linked.
  Proof.
    intros t v u [lp H] [lp' H']; 
      exists (lp ++ lp'); apply rel_chain_app with v; auto.
  Qed.

  Fixpoint plunge_and_flatten (n : nat) (ll : list (list path)) : list path :=
    match ll with
      | nil => nil
      | l::qq => (map (cons n) l) ++ (plunge_and_flatten (S n) qq)
    end.
  Property linked_congr : Congruence linked.
  Proof.
    intros f lt lu H.
    Lemma collect_paths : forall lt lu, forall2 linked lt lu -> 
      exists ll, forall3 rel_chain ll lt lu.
    Proof.
      intro lt; induction lt; intros; 
        destruct lu; simpl in *; try contradiction H.
      exists nil; exact I.
      destruct H as [Ha Hl]; assert (IH := IHlt lu Hl); clear IHlt Hl.
      destruct Ha as [pa Hla]; destruct IH as [ll Hll].
      exists (pa :: ll); simpl; tauto.
    Qed.
    generalize (collect_paths lt lu H); clear H; intros [ll Hll].
    exists (plunge_and_flatten O ll).
    Lemma plunge_rel_chain : 
      forall f lp t u pre post, rel_chain lp t u -> 
        rel_chain (map (cons (List.length pre)) lp)
        (app f (pre ++ (t :: post))) (app f (pre ++ (u :: post))).
    Proof.
      intro f; induction lp as [|p lp]; intros; simpl.
      inversion_clear H; constructor.
      inversion_clear H.
      assert (IH := IHlp v u pre post H1); clear IHlp.
      constructor 2 with (app f (pre ++ tcons v post)).
      clear IH H1.
      Lemma rel_at_terms_pre : 
        forall pre p t u post, rel_at p t u ->
          rel_at_terms (length pre) p
          (pre ++ (t :: post)) (pre ++ (u :: post)).
      Proof.
        induction pre; intros; simpl in *; constructor (auto).
      Qed.
      constructor 2; apply rel_at_terms_pre; assumption.
      assumption.
    Qed.
    Lemma plunge_and_flatten_linked : forall f ll n pre lt lu,
      forall3 rel_chain ll lt lu -> n = List.length pre ->
      rel_chain (plunge_and_flatten n ll)
      (app f (pre ++ lt)) (app f (pre ++ lu)).
    Proof.
      intros f; induction ll as [|lp ll]; intros; 
        destruct lt as [|t lt]; destruct lu as [|u lu]; 
          simpl in *; try contradiction; subst.
      constructor.
      destruct H; apply rel_chain_app with (app f (pre ++ (tcons u lt))).
      apply plunge_rel_chain; assumption.
      Lemma app_rev_fold : forall {A} (l l' : list A) (a : A),
        l ++ (a :: l') = (l ++ (a ::nil)) ++ l'.
      Proof.
        induction l; intros; simpl in *; auto.
        assert (IH := IHl l' a0); rewrite IH; auto.
      Qed.
      rewrite (app_rev_fold pre lt u), (app_rev_fold pre lu u).
      apply IHll; auto.
      rewrite app_length; simpl; omega.
    Qed.
    exact (plunge_and_flatten_linked f ll O nil lt lu
      Hll (refl_equal O)).
  Qed.

  (** We can then prove tha [linked] and [mext] are the same relations.
     The first inclusion is proven by a simple induction, the reverse
     inclusion is given by [smallest_closure] and the fact that [linked]
     is a congruence relation. *)
  Theorem mext_iff : forall t u, linked t u <-> mext t u.
  Proof.
    intros; split; intro H.
    destruct H as [lp Hlp].
    induction Hlp.
      apply mext_refl.
      apply mext_trans with v; auto.
      clear lp Hlp IHHlp u.
      induction H using rel_at_mutual_ind with
        (P := fun p t v H => mext t v)
        (P0 := fun n p lt lv H => mext_terms lt lv) (p := p).
      constructor (assumption).
      constructor (assumption).
      constructor (auto). clear; induction l; constructor (auto using mext_refl).
      constructor; auto; apply mext_refl.
    refine (smallest_closure _ 
      linked_refl linked_sym linked_trans linked_congr _ t u H).
    intros; exists (nil :: nil).
    constructor 2 with u0; constructor (assumption).
  Qed.

  (** So now we have an alternative, equivalent, characterization of the
     refl-sym-trans+congr closure performed by [mext], in the sense of a
     chain of atomic rewritings. *)
End WithRelation.
End GenericCongrClosure.

(** Preuve papier du dernier théoreme (pas celui de Fermat) :

   Supposons une relation R entre termes, et on s'intéresse à la congruence
   définie par [mext] sur (R + l'égalité via interprétation pour les
   termes bien typés notée ~), ou de manière équivalente à [linked] sur 
   cette même relation. On note ça a <->* b. On veut prouver que si a
   et b sont bien typés, a <->* b implique a ~ b, ie. que leurs 
   interpretations sont égales, sous certaines conditions sur R.

   Supposons que sur les termes bien typés, R est incluse dans ~.
   Supposons existe un canonizer K : term -> term, tel que pour tous termes
   u et v, u <->*_R v (ie. n'utilisant que des égalités de R) est équivalent
   à K u = K v. 
   Supposons aussi que pour tout u, u <->*_R K u.
   Supposons enfin que K préserve le caractère bien typé, et que
   pour tout u v bien typés, u ~ v -> K u ~ K v.

   Lemma 1 : K est idempotent.
   Proof.
     Soit u, par définition du canonizer, il suffit de noter que
     K u <->*_R u, ce qui donne K (K u) = K u.
   Qed.
   Lemma 1' : K(f(u1,....un)) = K(f(K u1, .... K un)).
   Proof.
     ...
   Qed.
   Lemma 2 : Soit u bien typé, alors u ~ K u.
   Proof.
     Par induction sur la structure du terme u, en regardant ce que
     fait K au cas par cas.
   Qed.
  
   Lemma 3 : Soit u et v tel que u ~[p] v, et tel que K u est bien typé.
     Alors, K v est bien typé et K u ~ K v.
   Proof.
     Par induction sur le chemin p.
     Si p = ., alors u ~ v et donc u bien typé et v bien typé. Par ppté
     du canonizer, on a K u ~ K v et en particulier K v bien typé.
     Si p = k.q, alors u = f(u1,... un), v = f(v1, ... vn),
     avec uk ~[q] vk et uj = vj pour tout j différent de k.
     Par hypothèse d'induction sur uk et vk, on a :
     (IH) K uk bien typé -> K vk bien typé et K uk ~ K vk.
     
     
   Qed.

   Theorem X : Soient u v deux termes, v bien typé et K u bien typé, 
     alors u <->* v implique K u ~ K v (ce qui fait sens puisque K u
     et K v sont bien typés).
   Proof.
     Par induction sur la suite de réécritures.
     Si u = v, alors K u = K v d'où le résultat.
     Si u <->[p] w et w <->* v, alors 2 cas :
       * soit la règle utilisée dans u <->[p] w est de R, auquel cas
         on a K u = K w donc K w est bien typé et par hypothèse d'induction
         on a K w ~ K v, d'où le résultat ;
       * soit la règle utilisée est ~, auquel cas...
         ... on a K w bien typé et K u ~ K w ... (lemme nedded !)
         On peut donc appliquer l'hypothèse de récurrence
         et on a K w ~ K v. Comme K u ~ K w, par transitivté on a le résultat.
   Qed.
   Corollary X' : Soient u v bien typés, u <->* v -> u ~ v.
   Proof.
     On a K u bien typé, donc d'apres X, on a K u ~ K v. Comme d'autre part,
     on a u ~ K u et v ~ K v par le lemme 2, on a le résultat.
   Qed.

*)

(* Module StepEquality. *)
(*   Import GenericCongrClosure. *)
(* (*   Variable M : varmaps. *) *)
(* (*   Let vty : type_env := varmaps_vty M. *) *)
(* (*   Let vsy : term_env vty := varmaps_vsy M. *) *)

(* (*   Notation "t :> ty" := (has_type vty vsy t ty = true)(at level 65). *) *)
(* (*   Notation "t :/> ty" := (has_type vty vsy t ty = false)(at level 65). *) *)

(* (*   Inductive step (u v : term) : Prop := *) *)
(* (*   | step_ring : ZRing u v -> step u v *) *)
(* (*   | step_wt : forall ty (Hu : u :> ty) (Hv : v :> ty), *) *)
(* (*       interp vty vsy u ty Hu = interp vty vsy v ty Hv -> step u v. *) *)

(*   Definition sanitize (M : varmaps) (t : term) : term := *)
(*     if wt t in M then t else *)
(*       match t with *)
(*         | app (Op DomainZ op) (cons a (cons b nil)) => *)
(*           match op with *)
(*             | Plus => *)
(*               if a == [0] then b *)
(*               else if b == topp a then [0] else t *)
(*             | Mult =>  *)
(*               if a == [1] then b else t *)
(*             | Div => *)
(*               match a with *)
(*                 | app (Op DomainZ Mult) (cons ku (cons u nil)) => *)
(*                   match ku with *)
(*                     | app (Cst DomainZ k) nil => *)
(*                       if b == [k] then if k == 0%Z then t else u else t *)
(*                     | _ => t *)
(*                   end *)
(*                 | _ => t *)
(*               end *)
(*             | _ => t *)
(*           end  *)
(*         | _ => t *)
(*       end. *)
(*   Remark sanitize_wt : forall M u, wt u in M = true -> sanitize M u = u. *)
(*   Proof. *)
(*     intros; unfold sanitize; rewrite H; reflexivity. *)
(*   Qed. *)
(*   Property sanitize_stable :  *)
(*     forall M u, ZRing u (sanitize M u) \/ u = sanitize M u. *)
(*   Proof. *)
(*     intros; set (su := sanitize M u) in *. *)
(*     unfold sanitize in su; destruct (wt u in M). *)
(*     right; reflexivity. *)
(*     destruct u as [f lt]; destruct f. *)
(*     right; reflexivity. *)
(*     right; reflexivity. *)
(*     destruct dom; try (right; reflexivity). *)
(*     destruct lt as [|a lt]; [right; reflexivity |]. *)
(*     destruct lt as [|b lt]; [right; reflexivity |]. *)
(*     destruct lt as [|? ?]; [| right; reflexivity]. *)
(*     destruct op; try (right; reflexivity). *)
(*     destruct (eq_dec a [0]). *)
(*     left; rewrite H; unfold su; constructor. *)
(*     destruct (eq_dec b (topp a)). *)
(*     left; rewrite H0; unfold su; constructor. *)
(*     right; reflexivity. *)
(*     destruct (eq_dec a [1]). *)
(*     left; rewrite H; unfold su; constructor. *)
(*     right; reflexivity. *)
(*     destruct a as [f lt]; destruct f; try (right; reflexivity). *)
(*     destruct dom; try (right; reflexivity). *)
(*     destruct op; try (right; reflexivity). *)
(*     destruct lt as [|ku lt]; [right; reflexivity |]. *)
(*     destruct lt as [|u lt]; [right; reflexivity |]. *)
(*     destruct lt as [|? ?]; [| right; reflexivity]. *)
(*     destruct ku as [g lu]; destruct g; try (right; reflexivity). *)
(*     destruct dom; try (right; reflexivity). *)
(*     destruct lu; [|right; reflexivity]. *)
(*     destruct (eq_dec b [z]); [|right; reflexivity]. *)
(*     destruct (eq_dec z 0%Z); [right; reflexivity |]. *)
(*     rewrite H; left; constructor; auto. *)
(*   Qed. *)

(*   Remark rel_at_or :  *)
(*     forall (R S T : term -> term -> Prop),  *)
(*       (forall u v, R u v <-> (S u v \/ T u v)) -> *)
(*       forall p u v, rel_at R p u v -> rel_at S p u v \/ rel_at T p u v. *)
(*   Proof. *)
(*     intros R S T Hiff p u v H. *)
(*     induction H using rel_at_mutual_ind with *)
(*       (P := fun p u v H => rel_at S p u v \/ rel_at T p u v) *)
(*       (P0 := fun n p lu lv H =>  *)
(*         rel_at_terms S n p lu lv \/ rel_at_terms T n p lu lv). *)
(*     rewrite Hiff in r; destruct r; [left | right]; constructor (assumption). *)
(*     destruct IHrel_at; [left | right]; constructor (assumption). *)
(*     destruct IHrel_at; [left | right]; constructor (assumption). *)
(*     destruct IHrel_at; [left | right]; constructor (assumption). *)
(*   Qed. *)

(*   (* Si  t <-> u, t bien typé et u mal typé,  *)
(*      alors la règle utilisée est dans ZRing *) *)
(*   Variable M : varmaps. *)
(*   Let vty : type_env := varmaps_vty M. *)
(*   Let vsy : term_env vty := varmaps_vsy M. *)

(*   Notation "t :> ty" := (has_type vty vsy t ty = true)(at level 65). *)
(*   Notation "t :/> ty" := (has_type vty vsy t ty = false)(at level 65). *)
(*   Definition ieq (u v : term) : Prop := *)
(*     exists ty, exists Hu : u :> ty, exists Hv : v :> ty, *)
(*         interp vty vsy u ty Hu = interp vty vsy v ty Hv. *)

(*   Inductive step (u v : term) : Prop := *)
(*   | step_ring1 : ZRing u v -> step u v *)
(*   | step_ring2 : ZRing v u -> step u v *)
(*   | step_wt : forall ty (Hu : u :> ty) (Hv : v :> ty), *)
(*       interp vty vsy u ty Hu = interp vty vsy v ty Hv -> step u v. *)

(*   Property step_iff : forall u v, *)
(*     step u v <-> (ZRing u v \/ (ZRing v u \/ ieq u v)). *)
(*   Proof. *)
(*     intros u v; split; intro H. *)
(*     destruct H; [ left | right; left | right; right ]; auto. *)
(*     exists ty; exists Hu; exists Hv; assumption. *)
(*     destruct H. constructor (assumption). *)
(*     destruct H. constructor (assumption). *)
(*     destruct H as [ty [x [y H]]]. *)
(*     constructor 3 with ty x y; assumption. *)
(*   Qed. *)

(*   Lemma rel_at_stable_type :  *)
(*     forall (R : term -> term -> Prop)  *)
(*       (HR : forall u v ty ty', R u v -> u :> ty -> v :> ty' -> ty = ty'), *)
(*     forall p u v ty ty', rel_at R p u v ->  *)
(*       u :> ty -> v :> ty' -> ty = ty'. *)
(*   Proof. *)
(*     intros r HR p u v ty ty' H; revert ty ty'. *)
(*     induction H using rel_at_mutual_ind with *)
(*       (P := fun p u v H => forall ty ty', u :> ty -> v :> ty' -> ty = ty') *)
(*       (P0 := fun n p lu lv H => forall tyf ty ty',  *)
(*         well_typed_terms vty vsy lu tyf ty -> *)
(*         well_typed_terms vty vsy lv tyf ty' -> ty = ty'). *)
(*     intros; exact (HR t u ty ty' r0 H H0). *)
(*     intros; apply has_type_1 in H; apply has_type_1 in H0. *)
(*     inversion_clear H; inversion_clear H0; exact (IHrel_at _ _ _ H1 H). *)
(*     intros. inversion H0; subst; clear H0. *)
(*     inversion H1; subst; clear H1. *)
(*     revert H4 H8; clear; revert t2; induction l; intros. *)
(*     inversion H4; inversion H8; subst; assumption. *)
(*     inversion H4; inversion H8; subst. *)
(*     inversion H10; subst; apply (IHl t0); assumption. *)
(*     intros; inversion H; inversion H0; subst. *)
(*     inversion H10; subst; eauto. *)
(*   Qed. *)
(*   Corollary rel_at_ieq_stable :  *)
(*     forall p u v ty ty', rel_at ieq p u v -> u :> ty -> v :> ty' -> ty = ty'. *)
(*   Proof. *)
(*     apply rel_at_stable_type; intros. *)
(*     destruct H as [ty0 [Hu [Hv _]]]. *)
(*     generalize (has_type_is_type_of _ _ _ _ Hu) *)
(*       (has_type_is_type_of _ _ _ _ H0); intros; subst. *)
(*     generalize (has_type_is_type_of _ _ _ _ H1); intros; subst. *)
(*     rewrite (has_type_is_type_of _ _ _ _ Hv); reflexivity. *)
(*   Qed. *)

(*   Lemma wt_rel_at_wt : *)
(*     forall p u v, rel_at ieq p u v -> wt u in M = true -> wt v in M = true. *)
(*   Proof. *)
(*     induction p; intros. *)
(*     inversion_clear H. *)
(*     destruct H1 as [ty [Ht [Hu H]]]. *)
(*     fold vty; fold vsy; rewrite <- (has_type_is_type_of _ _ _ _ Hu); auto. *)
(*     inversion H; subst; clear H. *)
(*     apply has_type_2; apply has_type_1 in H0; constructor. *)
(*     inversion H0; subst; clear H0; simpl in *. *)
(*     set (tyf := lookup_type (varmaps_vty M) (varmaps_vsy M) f) in *. *)
(*     clearbody tyf; revert p IHp lt lu H5 H3. *)
(*     induction a; intros; simpl in *. *)
(*     inversion H5; subst; clear H5. *)
(*     inversion H3; subst; clear H3; simpl in *; constructor; auto. *)
(*     apply has_type_2 in H6; apply has_type_1. *)
(*     assert (Hr := has_type_is_type_of _ _ _ _ H6); rewrite Hr in H6. *)
(*     assert (IH := IHp t u H H6). *)
(*     rewrite (rel_at_ieq_stable p t u _ _ H H6 IH) in Hr. *)
(*     rewrite Hr; assumption. *)
(*     inversion H5; subst; clear H5. *)
(*     inversion H3; subst; clear H3; simpl in *; constructor (eauto). *)
(*   Abort. *)
    


(* (*     Check well_typed_terms. *) *)
(* (*     intros p u v H; induction H using rel_at_mutual_ind with *) *)
(* (*       (P := fun p u v H => wt u in M = true -> wt v in M = true) *) *)
(* (*       (P0 := fun n p lu lv H => forall ty ty', *) *)
(* (*         well_typed_terms vty vsy lu ty ty' ->  *) *)
(* (*         well_typed_terms vty vsy lv ty ty'). *) *)
(* (*     destruct r as [ty [Ht [Hu H]]]. *) *)
(* (*     fold vty; fold vsy; rewrite <- (has_type_is_type_of _ _ _ _ Hu); auto. *) *)
(* (*     intro Z; apply has_type_2; apply has_type_1 in Z. *) *)
(* (*     inversion_clear Z; constructor. fold vty in *; fold vsy in *. *) *)
(* (*     simpl in *. Print types_of. *) *)
(* (*     exact (IHrel_at _ _ H). *) *)


(*   Lemma wt_eq_it_rule :  *)
(*     forall p u v, wt u in M = true -> wt v in M = false -> *)
(*       rel_at step p u v -> rel_at ZRing p u v. *)
(*   Proof. *)
(*     cut (forall p u v, wt u in M = true -> wt v in M = false -> *)
(*       rel_at step p u v ->  *)
(*       rel_at ZRing p u v \/ rel_at (fun u v => *)
(*         forall ty (Hu : u :> ty) (Hv : v :> ty), *)
(*           interp vty vsy u ty Hu = interp vty vsy v ty Hv) p u v). *)
(*     intro cut; intros. *)
(*     destruct (cut p u v H H0 H1). *)
(*     assumption. *)
(*     admit. *)
(*     intros; revert H H0. *)
(*   Abort. *)

(* (* *)
(*   t <->* u et t :> ty in M et u :> ty in M, alors  M(t) = M(u). *)
  
(*   Probablement par induction sur la taille (longueur ?) de la suite de *)
(*   réécritures. *)

(*   * si t = u, c évident *)
(*   * si t <-> u', u' <->* u,  *)
(*     - si u' est bien typé, il est forcément de type ty, *)
(*     on applique l'IH à u' et u, et par transitivité on a M(t) = M(u') = M(u). *)
(*     - si u' n'est pas bien typé... *)

(*     *) *)
(*   Inductive ring_term : term -> Prop := *)
(*   | ring_cst : forall k, ring_term [k] *)
(*   | ring_plus : forall u v, ring_term (u [+] v) *)
(*   | ring_mult : forall u v, ring_term (u [*] v) *)
(*   | ring_minus : forall u v, ring_term (u [-] v) *)
(*   | ring_opp : forall u, ring_term (topp u) *)
(*   | ring_div : forall u k, ring_term (u [/] [k]). *)
(*   Definition is_ring_term (t : term) := *)
(*     match t with *)
(*       | app (Cst DomainZ _) nil => true *)
(*       | app (Op DomainZ Opp) (cons _ nil) => true *)
(*       | app (Op DomainZ op) (cons _ (cons b nil)) => *)
(*         match op with  *)
(*           | Plus | Mult | Minus => true *)
(*           | Div =>  *)
(*             match b with | app (Cst DomainZ _) nil => true | _ => false end *)
(*           | _ => false *)
(*         end *)
(*       | _ => false *)
(*     end. *)

(*   Inductive is_ring_term_spec (t : term) : bool -> Prop := *)
(*   | is_ring_term_true :  *)
(*     forall (Hring : ring_term t), is_ring_term_spec t true *)
(*   | is_ring_term_false :  *)
(*     forall (Hring : ~ring_term t), is_ring_term_spec t false. *)
(*   Ltac prove_irt_spec := *)
(*     match goal with *)
(*       | |- is_ring_term_spec ?t false => *)
(*         solve [constructor; intro H; inversion H] *)
(*       | |- is_ring_term_spec ?t true => *)
(*         constructor; constructor *)
(*       | _ => fail "Not a goal of the form is_ring_term t b." *)
(*     end. *)
(*   Property is_ring_term_dec : forall t, is_ring_term_spec t (is_ring_term t). *)
(*   Proof. *)
(*     destruct t; destruct f; simpl. *)
(*     prove_irt_spec. *)
(*     destruct dom; try prove_irt_spec. *)
(*     destruct lt; prove_irt_spec. *)
(*     destruct dom; try prove_irt_spec. *)
(*     destruct op; repeat (destruct lt; try prove_irt_spec). *)
(*     destruct t0; try prove_irt_spec. *)
(*     destruct f; try destruct dom; try destruct lt; prove_irt_spec. *)
(*   Qed. *)
(*   Opaque is_ring_term. *)

(*   Inductive ring_subterms : term -> Prop := *)
(*   | ring_top : forall t, ring_term t -> ring_subterms t *)
(*   | ring_app : forall f lt t, List.In t lt ->  *)
(*     ring_subterms t -> ring_subterms (app f lt). *)
(*   Nested Fixpoint has_ring_subterms (t : term) : bool := *)
(*     if is_ring_term t then true *)
(*     else  *)
(*       match t with  *)
(*         | app _ lt => has_ring_subterms_terms lt *)
(*       end *)
(*   with has_ring_subterms_terms (lt : terms) : bool := *)
(*     match lt with *)
(*       | nil => false *)
(*       | t::q => if has_ring_subterms t then true  *)
(*         else has_ring_subterms_terms q *)
(*     end. *)

(*   Inductive has_ring_subterms_spec (t : term) : bool -> Prop := *)
(*   | has_ring_subterms_true :  *)
(*     forall (Hsubring : ring_subterms t), has_ring_subterms_spec t true *)
(*   | has_ring_subterms_false :  *)
(*     forall (Hsubring : ~ring_subterms t), has_ring_subterms_spec t false. *)
(*   Inductive has_ring_subterms_terms_spec (l : terms) : bool -> Prop := *)
(*   | has_ring_subterms_terms_true :  *)
(*     forall t (Hin : In t l) (Hsubring : ring_subterms t), *)
(*       has_ring_subterms_terms_spec l true *)
(*   | has_ring_subterms_terms_false :  *)
(*     forall (Hsubring : forall t, In t l -> ~ring_subterms t),  *)
(*       has_ring_subterms_terms_spec l false. *)

(*   Property has_ring_subterms_mutual_dec :  *)
(*     (forall t, has_ring_subterms_spec t (has_ring_subterms t)) /\ *)
(*     (forall l, has_ring_subterms_terms_spec l (has_ring_subterms_terms l)). *)
(*   Proof. *)
(*     apply term_mutual_ind. *)
(*     intros; simpl; unfold has_ring_subterms_terms in H. *)
(*     destruct H. *)
(*     match goal with | |- context f [if ?X then true else true] =>  *)
(*       let Z := context f [true] in  *)
(*       (cut Z; [intro cut; destruct X; exact cut |]) end. *)
(*     constructor; constructor 2 with t; assumption. *)
(*     destruct (is_ring_term_dec (app f lt)); constructor. *)
(*     constructor (assumption). *)
(*     intro abs; inversion abs; subst; auto. exact (Hsubring _ H1 H2). *)
(*     constructor; intros; contradiction. *)
(*     intros; simpl; destruct H. *)
(*     constructor 1 with t; intuition. *)
(*     destruct H0. *)
(*     constructor 1 with t0; intuition. *)
(*     constructor 2; intros; inversion H; subst; auto. *)
(*   Qed. *)
(*   Definition has_ring_subterms_dec :=  *)
(*     Eval simpl in (proj1 has_ring_subterms_mutual_dec). *)
(*   Opaque has_ring_subterms has_ring_subterms_terms has_type. *)

(*   Definition trou : term := [42]. *)
(*   Fixpoint cleanse (M : varmaps) (t : term) : term := *)
(*     if wt t in M then t *)
(*     else *)
(*       if has_ring_subterms t then *)
(*         match t with | app f l => *)
(*           app f (map (cleanse M) l) *)
(*         end *)
(*       else trou. *)
(*   Inductive cleanse_spec (M : varmaps) (t : term) : term  -> Prop := *)
(*   | cleanse_wt : *)
(*     forall (Hwt : wt t in M = true), cleanse_spec M t t *)
(*   | cleanse_subterms :  *)
(*     forall f l  *)
(*       (Hwt : wt t in M = false) (Hsub : ring_subterms t), *)
(*       cleanse_spec M t (app f (map (cleanse M) l)) *)
(*   | cleanse_hole :  *)
(*     forall (Hwt : wt t in M = false) (Hsub : ~ (ring_subterms t)), *)
(*       cleanse_spec M t trou. *)
(* (*   Property cleanse_dec : forall M t, cleanse_spec M t (cleanse M t). *) *)
(* (*   Proof. *) *)
(* (*     intros; destruct t as [f l]; unfold cleanse. *) *)
(* (*     destruct (wt (app f l) in M) as [ ]_eqn:Hwt. *) *)
(* (*     constructor 1; assumption. *) *)
(* (*     destruct (has_ring_subterms_dec (app f l)). *) *)
(* (*     constructor; assumption.  *) *)
(* (*     constructor; assumption. *) *)
(* (*   Qed. *) *)
(* End StepEquality. *)

Section IllTypedEqualities.
  Variable M : varmaps.

  Inductive bad_equality : term -> term -> Prop :=
  | bad_0_neutral : forall u, bad_equality u ([0][+]u)
  | bad_1_neutral : forall u, bad_equality u ([1][*]u)
  | bad_opp_cancel : forall u, bad_equality [0] (u[+]topp u)
  | bad_div_cancel : forall k u, k =/= 0%Z -> bad_equality u (([k][*]u)[/][k]).

  Theorem ill_typed_ZRing_1 : 
    forall t u, wt t in M = true -> wt u in M = false -> 
      ZRing t u -> bad_equality t u.
  Proof.
    intros t u Hwt Hit E; destruct E; try constructor; simpl in *;
      repeat (ite Hwt); repeat (ite Hit); congruence.
  Qed.
  Theorem ill_typed_ZRing_2 : 
    forall t u, wt t in M = false -> wt u in M = true -> 
      ZRing t u -> False.
  Proof.
    intros t u Hwt Hit E; destruct E; simpl in *;
      repeat (ite Hwt); repeat (ite Hit); try congruence.
    rewrite <- (has_type_is_type_of _ _ _ _ if0) in Hwt; congruence.
    rewrite <- (has_type_is_type_of _ _ _ _ if0) in Hwt; congruence.
    rewrite <- (has_type_is_type_of _ _ _ _ if1) in Hwt; congruence.
  Qed.



End IllTypedEqualities.


Section WithModelsAndR.
  Variable R : term -> term -> Prop.
  Variable M : varmaps.
  Let vty : type_env := varmaps_vty M.
  Let vsy : term_env vty := varmaps_vsy M.

  Notation "t :> ty" := (has_type vty vsy t ty = true)(at level 65).
  Notation "t :/> ty" := (has_type vty vsy t ty = false)(at level 65).
  
  Inductive mext : term -> term -> Prop :=
  | mext_wt :
    forall t u ty (Ht : t :> ty) (Hu : u :> ty),
      interp vty vsy t ty Ht = interp vty vsy u ty Hu -> mext t u
  | mext_refl : 
    forall t, mext t t
  | mext_sym :
    forall t u, mext u t -> mext t u
  | mext_trans :
    forall t v u, mext t v -> mext v u -> mext t u
  | mext_congr : 
    forall f lt lu, mext_terms lt lu -> mext (app f lt) (app f lu)
  | mext_rule : 
    forall t u, R t u -> mext t u
  with mext_terms : terms -> terms -> Prop :=
  | mext_nil :
    mext_terms nil nil
  | mext_cons : 
    forall t u lt lu,
      mext t u -> mext_terms lt lu -> mext_terms (t::lt) (u::lu).
  Generate Scheme mext.
End WithModelsAndR.

Definition eq := mext ZRing.
Definition eq_refl := mext_refl ZRing.
Definition eq_sym := mext_sym ZRing.
Definition eq_trans := mext_trans ZRing.
Definition eq_congr := mext_congr ZRing.

(* Notation "'types' 'of' f 'above' l 'in' M" := *)
(*   (types_of l (lookup_type (varmaps_vty M) (varmaps_vsy M) f))  *)
(*   (at level 1). *)
(* Notation "'wts' f 'above' l 'in' M" := *)
(*   (have_type (varmaps_vty M) (varmaps_vsy M)  *)
(*     l (lookup_type (varmaps_vty M) (varmaps_vsy M) f) *)
(*     (types of f above l in M)) *)
(*   (at level 1, l at level 200). *)
(* Section OnVerraBien. *)
(*   Variable M : varmaps. *)
(*   Notation vty := (varmaps_vty M). *)
(*   Notation vsy := (varmaps_vsy M). *)

(*   Definition P (u v : term) : eq M u v -> Prop := fun _ => *)
(*     match wt u in M, wt v in M with *)
(*       | true, true => Term.eq vty vsy u v *)
(*       | true, false =>        *)
(*         forall w, wt w in M = true -> eq M v w -> Term.eq vty vsy w u *)
(*       | false, true =>        *)
(*         forall w, wt w in M = true -> eq M u w -> Term.eq vty vsy w v *)
(*       | false, false => *)
(*         True *)
(* (*         forall w w', wt w in M = true -> wt w' in M = true ->  *) *)
(* (*           eq M u w -> eq M v w' -> Term.eq vty vsy w w' *) *)
(*     end. *)
(*   Definition Pl (lu lv : terms) :  mext_terms ZRing M lu lv -> Prop := fun _ => *)
(*     forall f, match wts f above lu in M, wts f above lv in M with *)
(*                 | true, true => eq_terms vty vsy lu lv *)
(*                 | true, false => True *)
(*                 | false, true => True *)
(*                 | false, false => *)
(*                   True *)
(*               end. *)
(*   Theorem P_is_true : forall u v (H : eq M u v), P u v H. *)
(*   Proof. *)
(*     unfold eq; apply (@mext_mutual_ind ZRing M P Pl);  *)
(*       unfold P in *; unfold Pl in *; intros. *)
(*     (* - int *) *)
(*     rewrite <- (has_type_is_type_of vty vsy t ty Ht), Ht. *)
(*     rewrite <- (has_type_is_type_of vty vsy u ty Hu), Hu. *)
(*     admit. (* ok *) *)
(*     (* - refl *) *)
(*     case_eq (wt t in M); intro Ht. *)
(*     apply Term.eq_refl.  *)
(*     trivial. *)
(*     (* - sym *) *)
(*     case_eq (wt t in M); intro Ht; *)
(*       case_eq (wt u in M); intro Hu; rewrite Ht, Hu in H; trivial. *)
(*     apply Term.eq_sym; assumption. *)
(*     (* - trans *) *)
(*     case_eq (wt t in M); intro Ht; *)
(*       case_eq (wt u in M); intro Hu;  *)
(*         case_eq (wt v in M); intro Hv;  *)
(*         rewrite ?Ht, ?Hu, ?Hv in *. *)
(*     apply Term.eq_trans with v; assumption. *)
(*     apply H0; auto; apply eq_sym; auto. *)
(*     intros; apply Term.eq_trans with v; auto using Term.eq_sym. *)
(*     intros; apply H; auto; apply eq_trans with u; assumption. *)
(*     intros; apply Term.eq_trans with v; auto using Term.eq_sym. *)
(*     intros; apply H0; auto; apply eq_trans with t; auto using eq_sym. *)
(*     trivial. *)
(*     trivial. *)
(*     (* - congr *) *)
(*     case_eq (wt app f lt in M); intro Ht; *)
(*       case_eq (wt app f lu in M); intro Hu. *)
(*     apply Term.eq_congr. *)
(*     assert (Hf := H f); clear H. *)
(*     change (wts f above lt in M = true) in Ht; rewrite Ht in Hf. *)
(*     change (wts f above lu in M = true) in Hu; rewrite Hu in Hf. *)
(*     assumption. *)
(*     admit. *)
(*     admit. *)
(*     trivial. *)
(*     (* - rule *) *)
(*     case_eq (wt t in M); intro Ht; *)
(*       case_eq (wt u in M); intro Hu. *)
(*     admit. (* ok *) *)
(*     admit. *)
(*     admit. *)
(*     trivial. *)
(*     (* - tnil *) *)
(*     assert (Hwt : wts f above tnil in M = true). *)
(*     simpl; apply tequal_2; reflexivity. *)
(*     rewrite Hwt; constructor. *)
(*     (* - tcons *) *)
    
(*   Qed. *)

(* End OnVerraBien. *)

Axiom eq_wt_iff : forall M t u,
  let vty := varmaps_vty M in
  let vsy := varmaps_vsy M in
    has_type vty vsy t (type_of vty vsy t) = true ->
    has_type vty vsy u (type_of vty vsy u) = true ->
    (eq M t u <-> Term.eq vty vsy t u).
  
Theorem eq_ring : forall M, @Ring_theory.ring_theory 
  term ([0]) ([1]) tplus tmult tminus topp (eq M).
Proof.
  intros; constructor; intros; try (apply mext_rule; constructor (auto));
    (apply mext_sym; apply mext_rule; constructor (auto)).
Qed.
Theorem eq_integral : forall M k u v, 
  eq M ([k][*]u) ([k][*]v) -> k =/= 0%Z -> eq M u v.
Proof.
  intros.
  apply eq_trans with (([k][*]u)[/][k]).
  apply mext_rule; constructor (assumption).
  apply eq_trans with (([k][*]v)[/][k]).
  apply eq_congr; repeat constructor (auto).
  apply mext_sym; apply mext_rule; constructor (assumption).
Qed.