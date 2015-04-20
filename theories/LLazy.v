(** This file contains the definitions of lazy literals. *)
Require Import Quote List Ergo Containers.OrderedType.
Require Import BinPos Literal.
Require Export Index DistrNeg.
Require Import Omega.
Require Containers.OrderedTypeEx TermUtils Containers.Generate.


Ltac discr := intros; discriminate.

(** * Preliminary results on list comparison  *)
(*    This section basically implements [list A] as an [OrderedType] *)
(*    where [A] is already an [OrderedType]. We will use it to *)
(*    compare lists and lists of lists of literals. *)
Section LtList.
  Variable A : Type.
  Variable ltA : A -> A -> Prop.
   
  Fixpoint lt_list (l l' : list A) : Prop :=
    match l, l' with
      | nil, nil => False
      | nil, _ => True
      | _, nil => False
      | cons a q, cons a' q' =>
        ltA a a' \/ (a = a' /\ lt_list q q')
    end.
      
  Variable compareA : A -> A -> comparison.
  Fixpoint compare_list (l l' : list A) : comparison :=
    match l, l' with
      | nil, nil => Eq
      | nil, _ => Lt
      | _, nil => Gt
      | cons a q, cons a' q' =>
        match compareA a a' with
          | Eq => compare_list q q'
          | Lt => Lt
          | Gt => Gt
        end
    end.
End LtList.

(** * A module type [LITERALBASE] from which 
   we can build expandable literals *)
(** * The module type [LITERAL] *)
Module Type LITERALBASE.
  Parameter t : Set.
  Declare Instance t_OT : UsualOrderedType t.

  (** Special literals for true and false *)
  Parameter ltrue : t.
  Parameter lfalse : t.

  (** Literals can be negated with the function [mk_not]. There are several
     axioms that this function must verify in order to be suitable: it must
     be a morphism for literal equality [eq], it shall be involutive,
     and no literal shall be equal to its negation. *)
  Parameter Inline mk_not : t -> t.

  Axiom mk_not_tf : mk_not ltrue = lfalse.
  Axiom mk_not_compat : forall l l', l = l' <-> mk_not l = mk_not l'.
  Axiom mk_not_invol : forall l, mk_not (mk_not l) = l.
  Axiom mk_not_fix : forall l, l = mk_not l -> False.

  (** Interpretation in an environment *)
  Parameter interp : varmaps -> t -> Prop.
  Axiom interp_mk_not : forall v l, ~~ (interp v l <-> ~ interp v (mk_not l)).
End LITERALBASE.

(** * The module [RAW]

   Module [RAW] is the first step in defining the lazy literals. 
   It corresponds to the literals as they would be defined in ML:
   a lazy literal is either an atomic literal [L idx b] identified
   by an index and a boolean, or a proxy [Proxy pos neg]. There are
   also special values for the true and false literals.

   The [Proxy] constructor expects two arguments: the first one 
   represents the formula that the proxy literal stands for, while
   the other one corresponds to the expansion of its negation. We
   proceed this way in order to be able to compute the negation of
   a literal in constant time, whether it is a proxy or not. So the
   second parameter of [Proxy] should just be seen as a memoization
   of the [mk_not] function.
*)
Module RAW (L : LITERALBASE).
  Inductive t_ : Set :=
  | Proxy (pos neg : list (list t_))
  | Lit (l : L.t).
  Definition t := t_.
  Let proxy := list (list t).

  (** We show handy induction principles for our type of literals.
     Since the recursive nature of [t] is 'hidden' under [list],
     the default induction principle created by Coq is basically
     useless. *)
  Section LiteralInduction.
    Variables
      (P : t -> Type)
      (Pl : list t -> Type)
      (Pp : proxy -> Type).
  
    Hypotheses
      (Hlit : forall l, P (Lit l))
      (Hview : forall p p', Pp p -> Pp p' -> P (Proxy p p'))
      
      (Hnil : Pl nil)
      (Hcons : forall a l, P a -> Pl l -> Pl (cons a l))

      (Hlnil : Pp nil)
      (Hlcons : forall l ll, Pl l -> Pp ll -> Pp (cons l ll)).
      
    Fixpoint literal_ind2 (l : t) : P l :=
      match l as x return P x with
        | Lit l => Hlit l
        | Proxy pos neg => 
          let l_aux := fun l =>
            ((fix l_ind (l : list t) : Pl l :=
              match l as x return Pl x with
                | nil => Hnil
                | cons t1 l1 =>
                  Hcons t1 l1 (literal_ind2 t1) (l_ind l1)
              end) l) 
            in
          let p_aux :=
            (fix ll_ind (ll : list (list t)) : Pp ll :=
              match ll as x return Pp x with
                | nil => Hlnil
                | cons l1 ll1 =>
                  Hlcons l1 ll1 (l_aux l1) (ll_ind ll1)
              end)
            in
          Hview pos neg (p_aux pos) (p_aux neg) 
      end.
  End LiteralInduction.
  Section LiteralInductionDefault.
    Variables
      (P : t -> Prop).
    Let Pl l := forall t, In t l -> P t.
    Let Pp ll := forall l, In l ll -> Pl l.

    Hypotheses
      (Hlit : forall l, P (Lit l))
      (Hview : forall p p', Pp p -> Pp p' -> P (Proxy p p')).

    Corollary literal_ind : forall (l : t), P l.
    Proof.
      refine (literal_ind2 P Pl Pp Hlit Hview _ _ _ _).
      abstract (unfold Pl; intros z Hz; contradiction Hz).
      abstract (intros a l Ha Hl; intros z Hz; destruct Hz; subst; auto).
      abstract (unfold Pp; intros z Hz; contradiction Hz).
      abstract (intros a l Ha Hl; intros z Hz; destruct Hz; subst; auto).
    Qed.
  End LiteralInductionDefault.

  (** Definitions of the [ltrue] and [lfalse] literals is straightforward. *)
  Definition ltrue := Lit L.ltrue.
  Definition lfalse := Lit L.lfalse.

  (** The negation function is simply negating the boolean for an atomic
     literal, and a swap of parameters for a proxy literal. *)
  Definition mk_not (l : t) :=
    match l with
      | Proxy pos neg => Proxy neg pos
      | Lit l => Lit (L.mk_not l)
    end.

  (** Expansion returns the first parameter of a [Proxy], and the empty
     list for an atomic literal. *)
  Definition expand (l : t) : list (list t) :=
    match l with
      | Proxy l _ => l
      | _ => nil
    end.

  (** We can define a notion of interpretation for literals, given  *)
  (*      a varmap [v] that assigns propositional values to indices. *)
  (*      It uses the [ll_interp] function defined in [DistrNeg]. *)
  Section Interp.
    Variable v : varmaps.
    Fixpoint interp (l : t) :=
      match l with
        | Lit l => L.interp v l
        | Proxy pos _ => ll_interp interp pos
      end.
    Definition cinterp := l_interp interp.
    Definition pinterp := ll_interp interp.
  End Interp.

  (** Parts for OrderedType *)
  Section OrderedType.
  Definition eq := @Logic.eq t.

  Fixpoint lt (x y : t) := 
    match x, y with
      | Lit l, Lit l' => l <<< l'
      | Lit _, _ => True
      | _, Lit _ => False
      | Proxy xpos xneg, Proxy ypos yneg =>
        lt_list (list t) (lt_list t lt) xpos ypos
    end.
  Notation llt := (lt_list t lt).
  Notation lllt := (lt_list _ llt).

  Property lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intro x; pattern x; apply literal_ind2 with 
      (Pl := fun lx => forall ly, llt lx ly -> ~ lx = ly)
      (Pp := fun llx => forall lly, lllt llx lly -> ~ llx = lly).
    destruct y; simpl; intuition. 
    discriminate. inversion H0; subst; order.
    destruct y; simpl; intuition. 
    inversion H2; subst; eauto.
    destruct ly; simpl; intuition. discriminate.
    destruct ly; simpl; intuition eauto; subst.
    inversion H2; subst; apply H with t0; auto; reflexivity.
    inversion H2; subst; eauto.
    destruct lly; simpl; intuition. discriminate.
    destruct lly; simpl; intuition eauto; inversion H2; subst; eauto.
  Qed.
  Property lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intro x; pattern x; apply literal_ind2 with 
      (Pl := fun lx => forall ly lz, llt lx ly -> llt ly lz -> llt lx lz)
      (Pp := fun llx => forall lly llz,
        lllt llx lly -> lllt lly llz -> lllt llx llz).
    destruct y; destruct z;  simpl; try (transitivity l0); tauto.
    destruct y; destruct z; simpl; intuition eauto.
    destruct ly; destruct lz; simpl; tauto.
    destruct ly; destruct lz; simpl; intuition eauto.
    left; rewrite <- H2; assumption.
    left; rewrite H1; assumption.
    right; split; eauto; congruence.
    destruct lly; destruct llz; simpl; tauto.
    destruct lly; destruct llz; simpl; intuition eauto.
    left; rewrite <- H2; assumption. 
    left; rewrite H1; assumption.
    right; split; eauto; congruence.
  Qed.

  (** ** Comparison on literals 

     This decidable comparison function for literals only
     compares the first part of [Proxy] constructors. This
     is for efficiency reasons of course, but this prevents
     us from proving that this is indeed a comparison
     function. Namely, nothing tells us that the second parameters
     are equal if and only if the first are. We will add the necessary
     invariant to our structure later on. *)
  Fixpoint compare_ (x y : t) : comparison :=
    match x, y with
      | Lit l, Lit l' => l =?= l'
      | Lit _, Proxy _ _ => Lt
      | Proxy _ _, Lit _ => Gt
      | Proxy xpos xneg, Proxy ypos yneg => 
        compare_list _ (compare_list _ compare_) xpos ypos
    end.
  End OrderedType.

  (** Properties of [mk_not] *)
  Property mk_not_invol : forall l, eq (mk_not (mk_not l)) l.
  Proof.
    intro x; pattern x; apply literal_ind.
    intro l; simpl; rewrite L.mk_not_invol; reflexivity.
    induction p; destruct p'; simpl; intros Hp Hp'; 
      intuition (auto; congruence).
  Qed.

  (** Expansion for proxies literals *)
  Property expand_compat : 
    forall l l', eq l l' -> eqlistA (eqlistA eq) (expand l) (expand l').
  Proof.
    intro x; pattern x; apply literal_ind; clear x.
    intro l; destruct l'; simpl; intuition. discriminate H.
    intros p p'; destruct l'; simpl; intuition.
    inversion H1; subst. 
    clear; induction pos; constructor; auto.
    clear; induction a; constructor; auto; reflexivity.
    discriminate H1.
  Qed.

  (** A suitable size function is 1 for atomic literals, and 1+n for 
     proxy literals, where n is the aggregated size of the first
     parameter of the proxy. *)
  Section ListSize.
    Variable A : Type.
    Variable sz : A -> nat.
    Fixpoint lsize (l : list A) := 
      match l with
        | nil => O
        | a::q => sz a + lsize q
      end.
  End ListSize.
  Section Size.
    Fixpoint size (l : t) :=
      match l with
        | Proxy pos _ => 
          S (lsize _ (lsize _ size) pos)
        | _ => 1
      end.

    Property size_m : forall l l', eq l l' -> size l = size l'.
    Proof.
      intros l l' H; rewrite H; reflexivity.
    Qed.
    Property size_pos : forall l, size l > 0.
    Proof. intros; destruct l; simpl; auto with arith. Qed.
  End Size.

  Definition llsize (ll : list (list t)) : nat :=
    lsize _ (lsize _ size) ll.
  Property size_expand : forall l, llsize (expand l) < size l.
  Proof. destruct l; simpl; auto with arith. Qed.
End RAW.

(** * The module [LLAZY]

   Because of the remark we made above about [RAW.compare_], we
   need to add some invariants to our literal structure. This will
   be the real type of literals used in the procedure.
*)
Module LLAZYFY (L : LITERALBASE) <: LITERAL.
  Module Import RAW := RAW L.

  Definition negation := distr_neg mk_not.
  Arguments In {A} a !l.

  (** The *big* lemma that states that negation has the
     meaning we have in mind. Its proof is in [DistrNeg]. *)
  Theorem negation_interp :
    forall f p, 
      (forall l c, In l c -> In c p -> ~~(f l <-> ~f (mk_not l))) ->
      ~~(ll_interp f p <-> ~ll_interp f (negation p)).
  Proof.
    apply negation_interp.
  Qed.

  (** A raw literal is well_formed if and only if :
     - it is an atomic literal
     - it stands for a [Proxy pos neg] where all literals
     in [pos] and [neg] are in turn well-formed, where [pos]
     and [neg] have the same size and are each other's image
     by the [negation] function.
     
     In particular, we require [negation] to be locally involutive
     on lists we use in proxies ; this is fundamental to our proofs.
     *)
  Inductive wf_lit : RAW.t -> Prop :=
  | wf_lit_lit : forall l, wf_lit (Lit l)
  | wf_lit_proxy : 
    forall pos neg, 
      negation pos = neg -> negation neg = pos -> 
      llsize pos = llsize neg ->
      (forall l t, In l pos -> In t l -> wf_lit t) ->
      (forall l t, In l neg -> In t l -> wf_lit t) ->
      wf_lit (Proxy pos neg).

  (** A weakened version of [wf_lit] which suffices to ensure
     well-formed expansion and well-founded induction on literals. *)
  Inductive wf_lit_weak : RAW.t -> Prop :=
  | wf_lit_wk_lit : forall l, wf_lit_weak (Lit l)
  | wf_lit_wk_proxy : 
    forall pos neg, 
      (forall l t, In l pos -> In t l -> wf_lit t) ->
      (forall l t, In l neg -> In t l -> wf_lit t) ->
      wf_lit_weak (Proxy pos neg).
  
  Remark wf_lit_2_weak : forall l, wf_lit l -> wf_lit_weak l.
  Proof.
    destruct l; intro Hwf; inversion Hwf; constructor; assumption.
  Qed.

  (** We are now ready to define our literal type [t]. It is
     just a dependent record packing a raw literal and a proof
     that it is well-formed together. *)
  Structure t_ : Type := mk_literal {
    this :> RAW.t;
    wf : wf_lit this
  }.
  Definition t := t_.

  (** We can now define the values expected by the [LITERAL] interface,
     starting with the easy ones : [ltrue] and [lfalse]. *)
  Definition ltrue := mk_literal (Lit L.ltrue) (wf_lit_lit L.ltrue).
  Definition lfalse := mk_literal (Lit L.lfalse) (wf_lit_lit L.lfalse).

  (** A corollary of the big theorem above is that the negation of  *)
  (*  a literal is indeed the negation of its literal. This is guaranteed *)
  (*  by the fact that if a proxy is well-formed, then its second parameter *)
  (*  is the [negation] of the first one. *)
  Lemma wf_negation : 
    forall v l, wf_lit l -> ~~(interp v l <-> ~interp v (RAW.mk_not l)).
  Proof.
    intros v l; pattern l; apply literal_ind; intros; simpl.
    apply L.interp_mk_not.
    inversion H1; intro N; apply (negation_interp (interp v) p).
    intros k c Hk Hc; apply (H c Hc k Hk (H7 c k Hc Hk)).
    intro R; crewrite R N; apply N.
    rewrite H4; reflexivity.
  Qed.

  Definition interp v (l : t) := interp v l.

  (** The negation of a well-formed literal is well-formed,
     this lets us lift the [mk_not] function from our raw literals
     to the well-formed literals. *)
  Property wf_mk_not : forall l, wf_lit l -> wf_lit (mk_not l).
  Proof.
    intros l Hwf; destruct l; simpl; 
      try constructor; inversion_clear Hwf; auto.
  Qed.
  Definition mk_not (l : t) : t := 
    mk_literal (mk_not l) (wf_mk_not l (wf l)).

  Corollary mk_not_interp :
    forall v (l : t), ~~(interp v l <-> ~(interp v (mk_not l))).
  Proof.
    intros v [x Hx]; simpl; apply wf_negation; auto.
  Qed.
  Definition interp_mk_not := mk_not_interp.
  
  (** The definition of [expand] is a little bit trickier since it
     requires traversing a proxy and adding proofs of well-formedness
     along the way. Indeed, the constructor [Proxy] contains raw literals
     and not well-formed ones, so we have to use the well-formed predicate
     recursively to return a list of list of well-formed literals. 

     This function is defined in proof style but with care so that
     it computes efficiently. *)
  Property wf_expand : forall l l' t, wf_lit_weak l ->
    In l' (expand l) -> In t l' -> wf_lit t.
  Proof.
    intros x; destruct x; intros l' t0 Hwf; inversion Hwf; subst;
      simpl in *; intuition; eauto.
  Qed.
  Definition expand (l : t) : list (list t).
  Proof.
    assert (Hwf := fun l' t => wf_expand l l' t (wf_lit_2_weak l (wf l))).
    destruct l as [x Hx]; destruct x; simpl in Hwf; clear Hx.
    clear neg; induction pos. exact nil.
    refine (cons _ (IHpos _)).
    assert (Ha := fun t => Hwf a t (or_introl _ (refl_equal a))).
    clear Hwf IHpos pos; induction a. exact nil.
    refine (cons _ (IHa _)).
    exact (mk_literal a (Ha a (or_introl _ (refl_equal a)))).
    exact (fun t0 Hin => Ha t0 (or_intror _ Hin)).
    refine (fun l' t0 Hin => Hwf l' t0 _). right; exact Hin.
    exact nil.
  Defined.

  (** Parts for OrderedType : note that the properties of [compare] 
     and [eq_dec] are guaranteed by the well-formedness invariant. *)
  Definition eq (l l' : t) := RAW.eq l l'.
  Definition lt (l l' : t) := RAW.lt l l'.

  Property eq_refl : forall x : t, eq x x.
  Proof. intros [x Hx]; unfold eq; reflexivity. Qed.
  Property eq_sym : forall x y : t, eq x y -> eq y x.
  Proof. intros [x Hx] [y Hy]; unfold eq; symmetry; auto. Qed.
  Property eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof. 
    intros [x Hx] [y Hy] [z Hz]; unfold eq; simpl; transitivity y; auto.
  Qed.

  Property lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. intros [x Hx] [y Hy] [z Hz]; unfold lt; apply lt_trans. Qed.
  Property lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. intros [x Hx] [y Hy]; unfold eq, lt; apply lt_not_eq. Qed.

  Notation llt := (lt_list _ RAW.lt).
  Notation lllt := (lt_list _ (lt_list _ RAW.lt)).

  Property compare_1 : 
    forall x y : RAW.t, wf_lit x -> wf_lit y -> compare_ x y = Eq -> RAW.eq x y.
  Proof.
    intro x; pattern x; apply literal_ind2 with
      (Pl := fun lx => forall ly, 
        (forall l, In l lx -> wf_lit l) -> (forall l, In l ly -> wf_lit l) ->
        compare_list RAW.t compare_ lx ly = Eq -> lx = ly)
      (Pp := fun llx => forall lly,
        (forall l c, In l c -> In c llx -> wf_lit l) ->
        (forall l c, In l c -> In c lly -> wf_lit l) ->
        compare_list _ (compare_list _ compare_) llx lly = Eq -> llx = lly).
    destruct y; simpl; try (intros; discr).
    destruct (compare_dec l l0); congruence.
    destruct y; simpl; try discr; intros Hx Hy Hlt.
    inversion Hx; inversion Hy; rewrite <- H3, <- H10, (H pos); eauto.
    reflexivity.
    destruct ly; simpl; auto; discr.
    destruct ly; simpl; auto; try discr; intros Hx Hy Hlt.
    case_eq (compare_ a t0); intro Hc; rewrite Hc in Hlt; try discr.
    rewrite (H t0); eauto. rewrite (H0 ly); eauto.
    destruct lly; simpl; auto; discr.
    destruct lly; simpl; auto; try discr; intros Hx Hy Hlt.
    case_eq (compare_list RAW.t compare_ l l0); intro Hc; rewrite Hc in Hlt; 
      try discr.
    rewrite (H l0); eauto. rewrite (H0 lly); eauto.
  Qed.
  Corollary compare_list_1 : forall lx ly,
    (forall l, In l lx -> wf_lit l) -> 
    (forall l, In l ly -> wf_lit l) -> 
    compare_list _ compare_ lx ly = Eq -> lx = ly.
  Proof.
    induction lx; destruct ly; simpl. auto.
    discr. discr.
    intros Hx Hy Hlt; case_eq (compare_ a t0); intro Hc; rewrite Hc in Hlt.
    rewrite (compare_1 a t0); eauto. rewrite (IHlx ly); eauto.
    discr. discr.
  Qed.
        
  Property compare_2 :
    forall x y : RAW.t, wf_lit x -> wf_lit y -> compare_ x y = Lt -> RAW.lt x y.
  Proof.
    intro x; pattern x; apply literal_ind2 with
      (Pl := fun lx =>
        forall ly, 
          (forall l, In l lx -> wf_lit l) -> (forall l, In l ly -> wf_lit l) ->
          compare_list RAW.t compare_ lx ly = Lt -> lt_list RAW.t RAW.lt lx ly)
      (Pp := fun llx => forall lly,
        (forall l c, In l c -> In c llx -> wf_lit l) ->
        (forall l c, In l c -> In c lly -> wf_lit l) ->        
        compare_list _ (compare_list RAW.t compare_) llx lly = Lt ->
        lt_list (list RAW.t) (lt_list RAW.t RAW.lt) llx lly).
    destruct y; simpl; try tauto.
    destruct (compare_dec l l0); intuition discriminate.
    destruct y; simpl; try discr; intros Hx Hy Hlt.
    inversion Hx; inversion Hy; apply (H pos); eauto.
    destruct ly; simpl; [discr | tauto].
    destruct ly; simpl; try discr; intros Hx Hy Hlt.
    case_eq (compare_ a t0); intro Hc; rewrite Hc in Hlt; try discr.
    right; split; [apply compare_1; eauto| apply (H0 ly); eauto].
    left; apply H; eauto.
    destruct lly; simpl; try discr; auto.
    destruct lly; simpl; try discr; intros Hx Hy Hlt.
    case_eq (compare_list RAW.t compare_ l l0); intro Hc; rewrite Hc in Hlt.
    right; split; [|apply (H0 lly); eauto].
    apply (compare_list_1 l l0); eauto.
    left; apply (H l0); eauto.
    discr.
  Qed.

  Property compare_3 :
    forall x y : RAW.t, wf_lit x -> wf_lit y -> compare_ x y = Gt -> RAW.lt y x.
  Proof.
    intro x; pattern x; apply literal_ind2 with
      (Pl := fun lx =>
        forall ly, 
          (forall l, In l lx -> wf_lit l) -> (forall l, In l ly -> wf_lit l) ->
          compare_list RAW.t compare_ lx ly = Gt -> lt_list RAW.t RAW.lt ly lx)
      (Pp := fun llx => forall lly,
        (forall l c, In l c -> In c llx -> wf_lit l) ->
        (forall l c, In l c -> In c lly -> wf_lit l) ->        
        compare_list _ (compare_list RAW.t compare_) llx lly = Gt ->
        lt_list (list RAW.t) (lt_list RAW.t RAW.lt) lly llx).
    destruct y; simpl; try discr.
    destruct (compare_dec l l0); intuition discr.
    destruct y; simpl; try discr; auto; intros Hx Hy Hlt.
    inversion Hx; inversion Hy; apply (H pos); eauto.
    destruct ly; simpl; discr.
    destruct ly; simpl; try discr; auto; intros Hx Hy Hlt.
    case_eq (compare_ a t0); intro Hc; rewrite Hc in Hlt; try discr.
    right; split; [rewrite (compare_1 a t0); eauto| apply (H0 ly); eauto].
    left; apply H; eauto.
    destruct lly; simpl; try discr; auto.
    destruct lly; simpl; try discr; auto; intros Hx Hy Hlt.
    case_eq (compare_list RAW.t compare_ l l0); intro Hc; rewrite Hc in Hlt.
    right; split; [|apply (H0 lly); eauto].
    rewrite (compare_list_1 l l0); eauto.
    left; apply (H l0); eauto.
    discr.
    left; apply (H l0); eauto.
  Qed.

  Instance t_OT : OrderedType t := {
    _eq := eq;
    _lt := lt;
    OT_Equivalence := @Build_Equivalence _ _ eq_refl eq_sym eq_trans;
    OT_StrictOrder := Build_StrictOrder _ _ _ _ lt_trans lt_not_eq;
    _cmp := compare_
  }.
  Proof.
    intros [x Hx] [y Hy]; simpl;
      case_eq (compare_ x y); intro Hcomp; constructor;
        [apply compare_1 | apply compare_2 | apply compare_3]; auto.
  Defined.

  (** Now we move on to proving the properties required by [LITERAL]. *)
  Property mk_not_tf : mk_not ltrue === lfalse.
  Proof. compute; rewrite L.mk_not_tf; reflexivity. Qed.

  Property mk_not_compat : forall l l', l === l' <-> mk_not l === mk_not l'.
  Proof.
    intros [x Hx] [y Hy].
    unfold equiv, _eq; simpl; unfold eq; compute; split.
    compute; intro H; rewrite H; reflexivity.
    revert y Hx Hy; pattern x; apply literal_ind; destruct y; simpl.
    discr. intros; inversion H.
    rewrite ((proj2 (L.mk_not_compat l l0)) H1); reflexivity.
    intros W1 W2; inversion W1; inversion W2; rewrite <- H3, <- H10.
    congruence.
    discr.
  Qed.
  Instance mk_not_m : Proper (_eq ==> _eq) mk_not.
  Proof.
    repeat intro; rewrite <- (mk_not_compat x y); assumption.
  Qed.
  Property mk_not_invol : forall l, mk_not (mk_not l) === l.
  Proof. 
    intro l; unfold equiv, _eq; simpl; unfold eq; simpl.
    exact (RAW.mk_not_invol l).
  Qed.
  Property mk_not_fix : forall l, l === (mk_not l) -> False.
  Proof.
    destruct l as [x Hx]; unfold equiv; simpl; unfold eq; simpl; intro Heq.
    apply (wf_negation empty_maps x Hx).
    destruct x; simpl in *.
    inversion Heq; subst.
    tauto.
    inversion Heq; intros _; exact (L.mk_not_fix l H0).
  Qed.

  (** Expansion for proxies literals *)
  Property expand_compat :
    forall l l', l === l' -> eqlistA (eqlistA _eq) (expand l) (expand l').
  Proof.
    intros [x Hx] [y Hy]; unfold eq in *; intros Heq; simpl in *.
    destruct x; destruct y; try discriminate Heq; try constructor.
    inversion Heq; subst; clear Heq.
    set (Hx_weak := fun l' t0 =>
      wf_expand (Proxy pos0 neg0) l' t0
      (wf_lit_2_weak (Proxy pos0 neg0) Hx)).
    fold Hx_weak; clearbody Hx_weak.
    set (Hy_weak := fun l' t0 =>
      wf_expand (Proxy pos0 neg0) l' t0
      (wf_lit_2_weak (Proxy pos0 neg0) Hy)).
    fold Hy_weak; clearbody Hy_weak; clear Hy Hx. unfold RAW.t.
    simpl in *;  clear neg0; induction pos0; simpl; constructor.
    clear IHpos0.
    set (Ha_weak := (fun t0 : RAW.t_ =>
         Hx_weak a t0
           (or_introl (In a _) (Logic.eq_refl)))) in |- *.
    fold (In a pos0) in *.
    change ((fun t0 : RAW.t_ =>
         Hx_weak a t0
           (or_introl (In a _) (Logic.eq_refl)))) with Ha_weak.
    clearbody Ha_weak; clear Hx_weak.
    set (Ha'_weak := (fun t0 : RAW.t_ =>
         Hy_weak a t0
           (or_introl
              (In a pos0) (refl_equal a)))).
    fold Ha'_weak; clearbody Ha'_weak; clear Hy_weak pos0.
    induction a; simpl; constructor.
    simpl; reflexivity. apply IHa.
    apply IHpos0.
  Qed.

  (** A lemma about interp and expand *)
  Property expand_map_map : 
    forall (l : t), eqlistA (eqlistA RAW.eq) 
      (List.map (List.map this) (expand l)) (RAW.expand l).
  Proof.
    intros [x Hx]; destruct x; try constructor.
    inversion Hx; simpl; clear H1 H2; subst.
    set (Hx_weak := fun l' t =>
      wf_expand (Proxy pos neg) l' t (wf_lit_2_weak (Proxy pos neg) Hx)).
    fold Hx_weak; clearbody Hx_weak; simpl in Hx_weak. unfold RAW.t.
    clear; induction pos; simpl; constructor.
    clear IHpos.
    set (Ha_weak := (fun t0 : RAW.t_ =>
         Hx_weak a t0
           (or_introl
              (In a pos) (refl_equal a)))) in *.
    change (fun t0 : RAW.t_ => Hx_weak a t0 (or_introl Logic.eq_refl))
           with Ha_weak in |- *.
    clearbody Ha_weak; clear Hx_weak.
    induction a; simpl; constructor. reflexivity.
    apply IHa.
    apply IHpos.
  Qed.

  (** Sizes *)
  Definition size (l : t) := size l.
  Instance size_m : Proper (_eq ==> @Logic.eq nat) size.
  Proof. repeat intro; apply size_m; auto. Qed.
  Property size_pos : forall l, size l > 0.
  Proof. intros; apply size_pos. Qed.
  Property size_mk_not : forall l, size (mk_not l) = size l.
  Proof.
    intros [x Hx]; destruct x; unfold size; simpl; auto.
    inversion Hx; unfold llsize in H3; rewrite H3; auto.
  Qed.
  Fixpoint lsize (l : list t) := 
    match l with
      | nil => O
      | a::q => size a + lsize q
    end.
  Fixpoint llsize (ll : list (list t)) :=
    match ll with
      | nil => O
      | C::qq => lsize C + llsize qq
    end.
  Lemma llsize_llsize : forall ll, llsize ll = RAW.llsize (map (map this) ll).
  Proof.
    induction ll; simpl; auto.
    f_equal; auto.
    clear IHll ll; induction a; simpl; auto.
  Qed.
  Lemma size_expand : 
    forall l, llsize (expand l) < size l.
  Proof.
    intros l.
    assert (Hl := expand_map_map l).
    cut (llsize (expand l) = RAW.llsize (RAW.expand l)).
    intro R; rewrite R; exact (size_expand l).
    revert Hl; generalize (RAW.expand l); generalize (expand l); clear l.
    induction l; destruct l; simpl; intros.
    reflexivity. inversion Hl.
    inversion Hl; subst. inversion H3; subst.
    revert H1; clear; revert x'; induction a; destruct x'; simpl; intros.
    reflexivity. inversion H1. inversion H1.
    inversion H1; subst. 
    simpl in IHa; generalize (IHa x' H5).
    unfold size; rewrite (RAW.size_m _ _ H3); omega.
    simpl in IHl; inversion Hl; subst; rewrite (IHl l'); auto.
    revert H1; clear; revert x' l'.
    induction a; destruct x'; simpl; intros.
    reflexivity. inversion H1. inversion H1.
    inversion H1; subst.
    simpl in IHa; generalize (IHa x' l' H5); auto.
    unfold size; rewrite (RAW.size_m _ _ H3); omega.
  Qed.

  (** Properties about proxies and expand 
     that are only necessary for completion*)
  Definition is_proxy (l : t) : bool :=
    match this l with
      | Proxy _ _ => true
      | _ => false
    end.
  Lemma is_proxy_mk_not : forall l, is_proxy l = is_proxy (mk_not l).
  Proof.
    intros [l lwf]; destruct l; reflexivity.
  Qed.
  Instance is_proxy_m : Proper (_eq ==> @Logic.eq bool) is_proxy.
  Proof.
    intros [l lwf] [k kwf]; destruct l; destruct k; intro H; vm_compute in H |- *.
    reflexivity. discr. discr. reflexivity.
  Qed.
  Lemma is_proxy_nil : forall l, is_proxy l = false -> expand l = nil.
  Proof.
    intros [l lwf]; destruct l; intro H; vm_compute in H; 
      try discriminate H; reflexivity.
  Qed.
  Lemma is_proxy_true : is_proxy ltrue = false.
  Proof.
    reflexivity.
  Qed.

  Section ExpandNot.
    Variable f : t -> Prop.
    Hypothesis f_m : forall l l', l === l' -> (f l <-> f l').

    Let fl :=
      (fix l_interp c :=
        match c with
          | nil => False
          | l::q => f l \/ l_interp q
        end).
    Let fll := 
      (fix ll_interp ll :=
        match ll with
          | nil => True
          | c::q => fl c /\ ll_interp q
        end).

    Remark eqlist_sym : forall A (eq : A -> A -> Prop), 
      (forall x y, eq x y -> eq y x) ->
      forall x y, eqlistA eq x y -> eqlistA eq y x.
    Proof.
      intros A e Hsym; induction x; destruct y; intros Hx; inversion Hx.
      constructor.
      subst; constructor.
      exact (Hsym _ _ H2).
      apply IHx; assumption.
    Qed.
    Remark eqlist_trans : forall A (eq : A -> A -> Prop), 
      (forall x y z, eq x y -> eq y z -> eq x z) ->
      forall x y z, eqlistA eq x y -> eqlistA eq y z -> eqlistA eq x z.
    Proof.
      intros A e Htrans; induction x; destruct y; destruct z;
        intros Hx Hy; inversion Hx; inversion Hy.
      constructor.
      subst; constructor.
      exact (Htrans _ _ _ H2 H8).
      apply IHx with y; assumption.
    Qed.
      
    Lemma eqlist_to_raw :
      forall l l', eqlistA _eq l l' <-> 
        eqlistA RAW.eq (map this l) (map this l').
    Proof.
      induction l; destruct l'; simpl; split;
        intro Heq; inversion Heq; subst; constructor; auto.
      rewrite <- IHl; assumption.
      rewrite IHl; assumption.
    Qed.
      
    Lemma eqlist2_to_raw :
      forall l l', eqlistA (eqlistA _eq) l l' <->
        eqlistA (eqlistA RAW.eq) (map (map this) l) (map (map this) l').
    Proof.
      induction l; destruct l'; simpl; split; 
        intro Heq; inversion Heq; subst; constructor.
      rewrite <- eqlist_to_raw; assumption.
      rewrite <- (IHl l'); assumption.
      rewrite eqlist_to_raw; assumption.
      rewrite (IHl l'); assumption.
    Qed.
      
    Lemma negate_expand :
      forall l, is_proxy l = true ->
        eqlistA (eqlistA _eq) (expand (mk_not l)) (distr_neg mk_not (expand l)).
    Proof.
      intros [l lwf] Hproxy; destruct l;
        vm_compute in Hproxy; try discr.
      assert (Heq := expand_map_map (mk_not (mk_literal (Proxy pos neg) lwf))).
      assert (Heq' := expand_map_map (mk_literal (Proxy pos neg) lwf)).
      simpl RAW.expand in *; revert Heq Heq'; clear Hproxy.
      generalize (expand (mk_not (mk_literal (Proxy pos neg) lwf))).
      generalize (expand (mk_literal (Proxy pos neg) lwf)).
      inversion lwf.
      assert (Hpos : negation (negation pos) = pos) by congruence.
      clear H H0 H2; revert Hpos; subst; clear; intro Hpos.
      intros P P' HP' HP; rewrite eqlist2_to_raw.
      refine (eqlist_trans _ _ (eqlist_trans _ _ _) _ _ _ HP' _).
      apply (@transitivity _ _ _).
      unfold negation; apply eqlist_sym in HP.
      2:(apply eqlist_sym; symmetry; auto).
      refine (eqlist_trans _ _ (eqlist_trans _ _ _) _ _ _
        (DistrNeg.distr_neg_m _ _ HP) _).
      apply (@transitivity _ _ _).
      intros; congruence.
      apply eqlist_sym; [apply eqlist_sym; symmetry; auto |].
      apply negation_compose.
      intros [l lwf]; destruct l; simpl; reflexivity; auto.
    Qed.
      
    Theorem expand_mk_not : 
      forall l, is_proxy l = true ->
        (forall k c, In c (expand l) -> In k c -> ~~(f k <-> ~f (mk_not k))) ->
        ~~(fll (expand l) <-> ~fll (expand (mk_not l))).
    Proof.
      intros l Hproxy IH.
      change (~~ (ll_interp f (expand l) <-> 
        ~ ll_interp f (expand (mk_not l)))).
      rewrite (interp_m f f_m (negate_expand l Hproxy)).
      apply DistrNeg.negation_interp.
      intros; apply IH with c; auto.
    Qed.
  End ExpandNot.

  (** Sets of literals, clauses... *)
  Import Sets.
  Notation lset := (@set t t_OT (@SetAVLInstance.SetAVL_FSet t t_OT)).
  Notation clause := (@set t t_OT (@SetListInstance.SetList_FSet t t_OT)).

  Definition clause_OT : OrderedType clause := SOT_as_OT.
  Existing Instance clause_OT.
  Notation cset := (@set clause clause_OT 
    (@SetListInstance.SetList_FSet clause clause_OT)).
End LLAZYFY.

(** An instantiation *)
Require ModelsRingExt.
Module LITINDEX <: LITERALBASE.
  Inductive atom : Set := 
  | Atom (a : INDEX.t)
  | Equation (u v : Term.term).
  Definition t := (option atom * bool)%type.

  (** ** [atom] as an [OrderedType] *)
  Section AtomOrderedType.
    Import OrderedTypeEx TermUtils Generate.
    Generate OrderedType atom. (* does not create a UOT *)

    Lemma atom_eq_iff : forall a a', atom_eq a a' <-> a = a'.
    Proof.
      induction a; destruct a'; split; intro H; 
        subst; try constructor; try inversion H; subst; auto.
      rewrite H2; auto. rewrite H3, H5; auto.
    Qed.

    Global Program Instance atom_UOT : UsualOrderedType atom := {
      SOT_lt := atom_lt;
      SOT_cmp := atom_cmp
    }.
    Next Obligation.
      constructor.
      exact atom_lt_trans.
      intros; change (x <> y); rewrite <- atom_eq_iff; 
        exact (atom_lt_irrefl _ _ H).
    Qed.
    Next Obligation.
      destruct (atom_compare_spec x y); constructor; auto.
      rewrite <- atom_eq_iff; assumption.
    Qed.
  End AtomOrderedType.

  Instance t_OT : UsualOrderedType t.
  unfold t; eauto with typeclass_instances.
  Defined.

  Definition ltrue : t := (None, true).
  Definition lfalse : t := (None, false).

  Definition mk_not (l : t) := (fst l, negb (snd l)).
  Property mk_not_tf : mk_not ltrue = lfalse.
  Proof. reflexivity. Qed.
  Property mk_not_compat :
    forall l l', l = l' <-> mk_not l = mk_not l'.
  Proof.
    destruct l; destruct l'; intuition.
    inversion H; unfold mk_not; simpl; subst.
    reflexivity.
    unfold mk_not in H; simpl in H; inversion H.
    destruct b; destruct b0; try discriminate; reflexivity.
  Qed.
  Property mk_not_invol : forall l, (mk_not (mk_not l)) = l.
  Proof.
    destruct l; unfold mk_not; simpl; destruct b; reflexivity.
  Qed.
  Property mk_not_fix : forall l, l = (mk_not l) -> False.
  Proof.
    destruct l; unfold mk_not; simpl; destruct b; intro H; simpl in H.
    inversion H; discriminate.
    inversion H; discriminate.
  Qed.

  Definition lookup v (idx : index) : Prop := varmap_find True idx v.
  Definition interp_atom (v : varmaps) (a : option atom) : Prop :=
    match a with
      | Some (Atom a) => lookup (varmaps_lits v) a
      | Some (Equation s1 s2) => ModelsRingExt.eq v s1 s2
      | None => True
    end.
  Definition interp (v : varmaps) (l : t) : Prop :=
    match l with
      | (a, true) => interp_atom v a
      | (a, false) => ~ interp_atom v a
    end.
  Property interp_mk_not :
    forall v l, ~~ (interp v l <-> ~ interp v (mk_not l)).
  Proof.
    intros v l N; destruct l; destruct o; destruct b; simpl in N; tauto.
  Qed.
End LITINDEX.
Module LLAZY := LLAZYFY LITINDEX.

(* (** An instantiation *) *)
(* Module LITINDEX <: LITERALBASE. *)
(*   Inductive t_ := *)
(*   | LT *)
(*   | LF *)
(*   | L (idx : INDEX.t) (b : bool). *)
(*   Definition t := t_. *)

(*   Inductive lt : t -> t -> Prop := *)
(*   | lt_LT_LF : lt LT LF *)
(*   | lt_LT_L : forall idx b, lt LT (L idx b) *)
(*   | lt_LF_L : forall idx b, lt LF (L idx b) *)
(*   | lt_L_L_1 : forall idx idx' b b', *)
(*     b <<< b' -> lt (L idx b) (L idx' b') *)
(*   | lt_L_L_2 : forall idx idx' b b', *)
(*     b === b' -> idx <<< idx' -> lt (L idx b) (L idx' b'). *)
(*   Program Instance lt_StrictOrder : StrictOrder lt (@Logic.eq t). *)
(*   Next Obligation. *)
(*     OrderedTypeEx.inductive_lexico_trans. *)
(*     constructor 5; OrderedTypeEx.solve_by_trans_modulo. *)
(*   Qed. *)
(*   Next Obligation. *)
(*     destruct x; destruct y; intro H2; *)
(*       inversion H; inversion H2; subst; intuition order. *)
(*   Qed. *)

(*   Definition cmp (l l' : t) : comparison := *)
(*     match l, l' with *)
(*       | LT, LT => Eq *)
(*       | LT, _ => Lt *)
(*       | _, LT => Gt *)
(*       | LF, LF => Eq *)
(*       | LF, _ => Lt *)
(*       | _, LF => Gt *)
(*       | L idx b, L idx' b' => *)
(*         match b =?= b' with *)
(*           | Lt => Lt *)
(*           | Gt => Gt *)
(*           | Eq => idx =?= idx' *)
(*         end *)
(*     end. *)
(* (*   Print cmp. *) *)
(*   Property cmp_1 : forall l l', cmp l l' = Lt -> lt l l'. *)
(*   Proof. *)
(*     destruct l; destruct l'; simpl; intro H; try discr; *)
(*       try solve [constructor]. *)
(*     destruct (compare_dec b b0). *)
(*     constructor; auto. *)
(*     constructor 5; auto; apply compare_1; auto. *)
(*     discriminate. *)
(*   Qed. *)
(*   Property cmp_2 : forall l l', cmp l l' = Eq -> eq l l'. *)
(*   Proof. *)
(*     destruct l; destruct l'; simpl; intro H; try discr; *)
(*       try solve [constructor]. *)
(*     destruct (compare_dec b b0); try discr; *)
(*       destruct (compare_dec idx idx0); try discr. *)
(*     rewrite H0, H1; auto. *)
(*   Qed. *)
(*   Property cmp_3 : forall l l', cmp l l' = Gt -> lt l' l. *)
(*   Proof. *)
(*     destruct l; destruct l'; simpl; intro H; try discr; *)
(*       try solve [constructor]. *)
(*     destruct (compare_dec b b0). *)
(*     discriminate. *)
(*     constructor 5; auto; apply compare_3; auto. *)
(*     constructor; auto. *)
(*   Qed. *)
  
(*   Program Instance t_OT : UsualOrderedType t := { *)
(*     SOT_lt := lt; *)
(*     SOT_StrictOrder := lt_StrictOrder; *)
(*     SOT_cmp := cmp *)
(*   }. *)
(*   Next Obligation. *)
(*     destruct x; destruct y; simpl; try repeat constructor. *)
(*     destruct (compare_dec b b0); try repeat constructor; auto. *)
(*     destruct (compare_dec idx idx0); constructor. *)
(*     constructor 5; auto. *)
(*     rewrite H, H0; auto. *)
(*     constructor 5; auto. *)
(*   Qed. *)

(*   Definition ltrue : t := LT. *)
(*   Definition lfalse : t := LF. *)

(*   Definition mk_not (l : t) := *)
(*     match l with *)
(*       | LT => LF | LF => LT *)
(*       | L idx b => L idx (negb b) *)
(*     end. *)
(*   Property mk_not_tf : mk_not ltrue = lfalse. *)
(*   Proof. reflexivity. Qed. *)
(*   Property mk_not_compat : *)
(*     forall l l', l = l' <-> mk_not l = mk_not l'. *)
(*   Proof. *)
(*     destruct l; destruct l'; intuition (try discr). *)
(*     congruence. *)
(*     simpl in H; inversion H; subst. *)
(*     destruct b; destruct b0; intuition discr. *)
(*   Qed. *)
(*   Property mk_not_invol : forall l, (mk_not (mk_not l)) = l. *)
(*   Proof. *)
(*     destruct l; unfold mk_not; simpl; auto; *)
(*       destruct b; reflexivity. *)
(*   Qed. *)
(*   Property mk_not_fix : forall l, l = (mk_not l) -> False. *)
(*   Proof. *)
(*     destruct l; unfold mk_not; simpl; try discr; *)
(*       destruct b; intro H; simpl in H. *)
(*     inversion H; discriminate. *)
(*     inversion H; discriminate. *)
(*   Qed. *)
  
(*   Definition lookup v (idx : index) : Prop := varmap_find True idx v. *)
(*   Definition interp (v : varmap Prop) (l : t) : Prop := *)
(*     match l with *)
(*       | LT => True *)
(*       | LF => False *)
(*       | L idx true => lookup v idx *)
(*       | L idx false => ~ lookup v idx *)
(*     end. *)
(*   Property interp_mk_not : *)
(*     forall v l, ~~ (interp v l <-> ~ interp v (mk_not l)). *)
(*   Proof. *)
(*     intros v l N; destruct l; simpl in N; try tauto. *)
(*     destruct b; simpl in *; try tauto. *)
(*   Qed. *)
(* End LITINDEX. *)
(* Module LLAZY := LLAZYFY LITINDEX. *)
