(** This module contains the formalization of semantics. *)
Require Import Literal Containers.Sets List.

(** * The module type [SEM_INTERFACE] *)
(** This module type is parameterized by a [LITERAL] module, 
   introduces a notion of model and contains semantical 
   definitions about literals and formulas. *)
Module Type SEM_INTERFACE (L : LITERAL).
  (** Roughly speaking, a model is something that can be seen as 
     a function from literals to Prop. In particular a model, 
     unlike a partial assignment, assigns a propositional value 
     to every literal. *)
  Parameter model : Type.
  Parameter model_as_fun : model -> (L.t -> Prop).
  Coercion model_as_fun : model >-> Funclass.
  
  Import L.
  
  (** But in order to be interesting (and meaningful)
     models shoud have a certain number of properties. *)
  Section WF.
    Variable M : model.
    (** - first, a model should be total, ie. a literal should be true
       as soon as its negation is false. Nevertheless, we only require
       the double negation of this property, because otherwise it would
       amount to requiring classical reasoning *)
    Axiom full : forall l, ~~(~(M l) -> M (L.mk_not l)).
    (** - it should also be consistent, ie. it should not assign true values
       to both a literal and its negation *)
    Axiom consistent : forall l, M l -> ~(M (L.mk_not l)).
    (** - it should be compatible with literal equality *)
    Axiom morphism : forall l l', l === l' -> (M l <-> M l').
    (** - it always contains the special true literal
       (and by [consistent] and [L.mk_not_tf], does not
       contain the special false literal) *)
    Axiom wf_true : M ltrue.
    (** - finally, it should be compatible with the [expand] function.
       That is once again a particularity of our formalization : it states
       that the assignment of a proxy-literal should be consistent with
       the assignment of the literals that appear in its expansion.
       For example, if [X] expands to [[[A];[B]]], ie. [A /\ B], [X] should
       not be true if [A] or [B] isn't.
       *)
    Axiom wf_expand :
      forall l, M l -> 
        (forall c, In c (expand l) -> exists l', In l' c /\ M l').
  End WF.

(*   (* For completion *) *)
(*   Section Creation. *)
(*     Parameter model_of :  *)
(*       forall (m : L.t -> Prop) *)
(*         (Hfull : forall l, ~~(~(m l) -> m (L.mk_not l))) *)
(*         (Hconsistent : forall l, m l -> ~(m (L.mk_not l))) *)
(*         (Hmorphism : forall l l', l === l' -> (m l <-> m l')) *)
(*         (Htrue : m ltrue) *)
(*         (Hexpand : forall l, m l ->  *)
(*           (forall c, In c (expand l) -> exists l', In l' c /\ m l')), model. *)

(*     Axiom model_as_model_of :  *)
(*       forall m Hfull Hconsistent Hmorphism Htrue Hexpand l, *)
(*         model_as_fun  *)
(*         (model_of m Hfull Hconsistent Hmorphism Htrue Hexpand) l = m l. *)
(*   End Creation. *)

  (** Given these definitions, we can define what it means
     for a model to model a clause, a set of clauses,
     a set of literals and incompatiblity: *)
  Definition sat_clause (M : model) (C : clause) :=
    exists l, M l /\ l \In C.

  Definition sat_goal (M : model) (D : cset) :=
    forall C, C \In D -> sat_clause M C.

  Definition submodel (G : lset) (M : model) :=
    forall l, l \In G -> M l.

  Definition incompatible (G : lset) (D : cset) :=
    forall (M : model), submodel G M -> ~sat_goal M D.
 
  (** We also need some similar semantical definitions for
     partial assignments instead of models. *)
  Definition sat_clause_p (M : lset) (C : clause) :=
    exists l, l \In M /\ l \In C.

  Definition sat_goal_p (M : lset) (D : cset) :=
    forall C, C \In D -> sat_clause_p M C.
End SEM_INTERFACE.
  
(** * The functor [SEMANTICS] *)
(** The functor [SEMANTICS] is just a straightforward 
   implementation of the module type [SEM_INTERFACE] for
   propositional literals.*)
Module SEMANTICS (L : LITERAL) <: SEM_INTERFACE L.

  Definition model_ := L.t -> Prop.

  Import L.
  Module WF.
    Definition full (M : L.t -> Prop) : Prop :=
      forall l, ~~(~(M l) -> M (L.mk_not l)).

    Definition consistent (M : L.t -> Prop) : Prop :=
      forall l, M l -> ~(M (L.mk_not l)).

    Definition morphism (M : L.t -> Prop) : Prop :=
      forall l l', l === l' -> (M l <-> M l').

    Definition wf_true (M : L.t -> Prop) : Prop := M ltrue.

    Definition wf_expand (M : L.t -> Prop) : Prop :=
      forall l, M l -> 
        (forall c, In c (expand l) -> exists l', In l' c /\ M l').
  End WF.

  Structure model_with_props := mk_model {
    this : t -> Prop;
    this_full : WF.full this;
    this_wf : WF.consistent this;
    this_m : WF.morphism this;
    this_true : WF.wf_true this;
    this_expand : WF.wf_expand this
  }.
  Definition model := model_with_props.
  Definition model_as_fun (M : model) : t -> Prop := this M.
  Coercion model_as_fun : model >-> Funclass.

  Definition full : forall (M : model) l, ~~(~(M l) -> M (L.mk_not l)) :=
    this_full.
  Definition consistent : forall (M : model) l, M l -> ~(M (L.mk_not l)) :=
    this_wf.
  Definition morphism : forall (M : model) l l', l === l' -> (M l <-> M l') :=
    this_m.
  Definition wf_true : forall (M : model), M L.ltrue := 
    this_true.
  Definition wf_expand : forall (M : model) l, M l -> 
    (forall c, In c (expand l) -> exists l', In l' c /\ M l') :=
    this_expand.

  Section Creation.
    Variable m : L.t -> Prop.
    Hypothesis Hfull : forall l, ~~(~(m l) -> m (L.mk_not l)).
    Hypothesis Hconsistent : forall l, m l -> ~(m (L.mk_not l)).
    Hypothesis Hmorphism : forall l l', l === l' -> (m l <-> m l').
    Hypothesis Htrue : m ltrue.
    Hypothesis Hexpand : forall l, m l -> 
      (forall c, In c (expand l) -> exists l', In l' c /\ m l').

    Definition model_of : model := 
      @mk_model m Hfull Hconsistent Hmorphism Htrue Hexpand.
    Property model_as_model_of : forall l, model_as_fun model_of l = m l.
    Proof. intro; reflexivity. Qed.
  End Creation.

  Definition sat_clause (M : model) (C : clause) :=
    exists l, M l /\ l \In C.

  Definition sat_goal (M : model) (D : cset) :=
    forall C, C \In D -> sat_clause M C.

  Definition submodel (G : lset) (M : model) :=
    forall l, l \In G -> M l.

  Definition incompatible (G : lset) (D : cset) :=
    forall (M : model), submodel G M -> ~sat_goal M D.
  
  Definition sat_clause_p (M : lset) (C : clause) :=
    exists l, l \In M /\ l \In C.

  Definition sat_goal_p (M : lset) (D : cset) :=
    forall C, C \In D -> sat_clause_p M C.
End SEMANTICS.

(** * The functor [SemFacts] *)
Module SemFacts (L : LITERAL)(Import S : SEM_INTERFACE L).
  (** ** Model properties
     
     The functor [SemFacts] derives a couple of easy properties from
     a semantic interface, in order to quickly access the specification 
     part of a model. *)
  Fact model_m : forall (M : model) (l l' : L.t), 
    l === l' -> M l -> M l'.
  Proof.
    intros; rewrite <- (morphism M l l' H); exact H0.
  Qed.
  
  Fact model_em : forall (M : model) (l : L.t),
    M l -> M (L.mk_not l) -> False.
  Proof.
    intros; exact (consistent M l H H0).
  Qed.

  Fact model_full : forall (M : model) (l : L.t),
    ~~(~(M l) -> M (L.mk_not l)).
  Proof.    
    intros; exact (full M l).
  Qed.

  Fact model_true : forall (M : model), M L.ltrue.
  Proof. exact wf_true. Qed.

  Fact model_expand : 
    forall (M : model) (l : L.t), M l -> 
      (forall c, In c (L.expand l) -> exists l', In l' c /\ M l').
  Proof. exact wf_expand. Qed.

  (** An easy but useful remark *)
  Remark submodel_empty : forall (M : model), submodel {} M.
  Proof.
    unfold submodel; intros M l H.
    contradiction (empty_1 H).
  Qed.

(*   (** ** Completion of a well-formed partial assignment *) *)
(*   (** This section is a bit technical. It aims at completing *)
(*      a partial assignment as returned by the SAT procedure *)
(*      into a total model as defined in [SEMANTICS]. *)
(*      This shows that when [dpll] does not return [Unsat], there indeed *)
(*      exists a model of the formula.  *)
(*      *) *)
(*   Section Completion. *)
(*     Import F. *)
(*     Require Import Wf Wf_nat. *)
    
(*     Let Llt x y := L.size x < L.size y. *)
(*     Lemma Llt_wf : Wf.well_founded Llt. *)
(*     Proof. *)
(*       apply Wf_nat.well_founded_lt_compat with (f:=L.size); auto. *)
(*     Qed. *)
(*     Lemma Llt_expand : *)
(*       forall l c y, List.In c (L.expand l) -> List.In y c -> Llt y l. *)
(*     Proof. *)
(*       intros l; assert (Hl := L.size_expand l); revert Hl. *)
(*       generalize (L.expand l); intro ll; induction ll; intros Hlt c y Hc Hy. *)
(*       inversion Hc. *)
(*       inversion Hc; subst; simpl in Hlt. *)
(*       revert Hy Hlt; clear; generalize c; clear c; induction c; simpl. *)
(*       intro; contradiction. *)
(*       intro H; destruct H; subst. *)
(*       unfold Llt; rewrite (plus_n_O (L.size y)) at 2; clear; omega. *)
(*       assert (IH := IHc H); clear IHc. *)
(*       intro Ha; apply IH. revert Ha; clear. *)
(*       intros; omega. *)
(*       apply IHll with c; auto. *)
(*       clear IHll Hc H; revert ll Hlt; clear. *)
(*       induction a; simpl; intros; auto. *)
(*       apply IHa; omega. *)
(*     Qed. *)

(*     Section ExpandInduction. *)
(*       Variables *)
(*         (P : L.t -> Type) *)
(*         (Pl : list L.t -> Type) *)
(*         (Pp : list (list L.t) -> Type). *)
      
(*       Hypotheses *)
(*         (Hlift : forall l, Pp (L.expand l) -> P l) *)
        
(*         (Hnil : Pl nil) *)
(*         (Hcons : forall a l, P a -> Pl l -> Pl (cons a l)) *)
        
(*         (Hlnil : Pp nil) *)
(*         (Hlcons : forall l ll, Pl l -> Pp ll -> Pp (cons l ll)). *)
      
(*       Definition expand_induction : forall l, P l. *)
(*       Proof. *)
(*         intros l. *)
(*         apply (Wf.well_founded_induction_type Llt_wf); clear l. *)
(*         intros l IHl. *)
(* (*         refine (Hlift l *) *)
(* (*           ((fix ll_ind (l' : list (list L.t)) *) *)
(* (*             (llT : forall c y, In c l' -> In y c ->  Llt y l) : Pp l' := *) *)
(* (*             (match l' as a return *) *)
(* (*                (forall c y, In c a -> *) *)
(* (*                  In y c -> (fun y => Llt y l) y) -> Pp a with *) *)
(* (*                | nil => fun _ => Hlnil *) *)
(* (*                | c::ll => *) *)
(* (*                  (fun llT => Hlcons c ll *) *)
(* (*                    ((fix l_ind (l' : list L.t) *) *)
(* (*                      (lT : forall y, In y l' -> Llt y l) {struct l'} : Pl l' := *) *)
(* (*                      (match l' as a return *) *)
(* (*                         (forall y, In y a -> (fun y => Llt y l) y) -> Pl a with *) *)
(* (*                         | nil => fun _ => Hnil *) *)
(* (*                         | y::l => fun lT => *) *)
(* (*                           Hcons y l (IHl y _) (l_ind l _) *) *)
(* (*                       end) lT) c _) *) *)
(* (*                    (ll_ind ll _)) *) *)
(* (*              end) llT) (L.expand l) (Llt_expand l))). *) *)
(*         apply Hlift. *)
(*         generalize (Llt_expand l); generalize (L.expand l); *)
(*           intro ll; induction ll; intros Hlt. *)
(*         exact Hlnil. *)
(*         refine (Hlcons a ll _ (IHll _)). *)
(*         assert (Ha := fun y => Hlt a y (or_introl _ (refl_equal a))). *)
(*         clear Hlt; revert a Ha; induction a; intros Hlt. *)
(*         exact Hnil. *)
(*         refine (Hcons a a0 (IHl a _) (IHa _)). *)
(*         apply Hlt; intuition. *)
(*         intros; apply Hlt; intuition. *)
(*         intros; apply Hlt with c; intuition. *)
(*       Defined. *)
(*     End ExpandInduction. *)

(*     (** Pas trivial de faire ce genre de preuves sans proof irrelevance ! *) *)
(*     Theorem expand_induction_unfold : *)
(*       forall P Pl Pp H Hnil Hcons Hlnil Hlcons l, *)
(*         let lind := expand_induction P Pl Pp H Hnil Hcons Hlnil Hlcons in *)
(*           lind l = H l *)
(*           ((fix ll_ind (l' : list (list L.t)) : Pp l' := *)
(*             match l' with *)
(*               | nil => Hlnil *)
(*               | c :: ll => Hlcons c ll *)
(*                 ((fix l_ind (l' : list L.t) : Pl l' := *)
(*                   match l' with *)
(*                     | nil => Hnil *)
(*                     | a :: l => Hcons a l (lind a) (l_ind l) *)
(*                   end) c) *)
(*                 (ll_ind ll) *)
(*             end) (L.expand l)). *)
(*     Proof. *)
(*       intros; unfold lind; simpl. *)
(*       unfold expand_induction. *)
(*       unfold well_founded_induction_type. *)
(*       unfold Acc_rect. *)
(*       match goal with *)
(*         |- ?F l (Llt_wf l) = H l _ => set (f := F) *)
(*       end. *)
      
(*       assert (Hf_eq : forall x (Hx Hx' : Acc Llt x), f x Hx = f x Hx'). *)
(*       intros x. *)
(*       destruct Hx using Acc_inv_dep. *)
(*       destruct Hx' using Acc_inv_dep. *)
(*       simpl; f_equal. *)
(*       pose (Lrec := Llt_expand x); fold Lrec; clearbody Lrec. *)
(*       revert Lrec; generalize (L.expand x); induction l0; intros. *)
(*       reflexivity. *)
(*       simpl; rewrite IHl0; f_equal. *)
(*       clear IHl0. *)
(*       pose (arec :=      (fun y : L.t => *)
(*         Lrec a1 y *)
(*         (or_introl *)
(*           ((fix In (a2 : list L.t) (l1 : list (list L.t)) {struct l1} : *)
(*             Prop := *)
(*             match l1 with *)
(*               | nil => False *)
(*               | b :: m => b = a2 \/ In a2 m *)
(*             end) a1 l0) (refl_equal a1)))); fold arec. *)
(*       clearbody arec. clear Lrec. induction a1. *)
(*       reflexivity. *)
(*       simpl; f_equal. *)
(*       apply H0. *)
(*       apply IHa1. *)
      
(*       case_eq (Llt_wf l); intros. *)
(*       simpl f at 1; apply f_equal. *)
(*       pose (Lrec := Llt_expand l); fold Lrec; clearbody Lrec. *)
(*       revert Lrec; generalize (L.expand l). *)
(*       intro ll; induction ll; intros. *)
(*       reflexivity. *)
(*       simpl; rewrite IHll; f_equal. *)
(*       set (arec := *)
(*         (fun y : L.t => Lrec a0 y *)
(*           (or_introl *)
(*             ((fix In (a1 : list L.t) (l0 : list (list L.t)) {struct l0} : *)
(*               Prop := *)
(*               match l0 with *)
(*                 | nil => False *)
(*                 | b :: m => b = a1 \/ In a1 m *)
(*               end) a0 ll) (refl_equal a0)))). *)
(*       clearbody arec; clear IHll Lrec; revert arec. *)
(*       induction a0. *)
(*       reflexivity. *)
(*       intros; simpl. *)
(*       rewrite IHa0; f_equal. *)
(*       apply Hf_eq. *)
(*     Qed. *)
    
(*     Variable M : lset. *)
(*     Hypothesis Mwf : forall l, l \In M -> (L.mk_not l) \In M -> False. *)
(*     Hypothesis Mtrue : L.ltrue \In M. *)
(*     Hypothesis Mexpand : forall l, l \In M -> *)
(*       (forall c, List.In c (L.expand l) -> exists y, List.In y c /\ y \In M). *)
    
(*     (** Later, we need to build a total model from the partial model M. *)
(*        In order to do so, we need to satisfy the axioms of a model. *)
(*        Well-formedness follows from the well-formedness of the context, *)
(*        but for totalness M must be completed in an arbitrary way on unbound *)
(*        literals. To distinguish between a literal [l] and its negation *)
(*        [L.mk_not l], we use the total order [L.lt] on literal. Any other way *)
(*        to "choose" between a literal and its negation would work as well. *) *)
(*     Definition completion (l : L.t) : Prop := *)
(*       @expand_induction (fun _ => Prop) (fun _ => Prop) (fun _ => Prop) *)
(*         (fun l A => *)
(*           if l \in M then True *)
(*             else if L.mk_not l \in M then False *)
(*               else *)
(*                 if L.is_proxy l then A else l <<< (L.mk_not l)) *)
(*         False (fun _ _ => or) *)
(*         True (fun _ _ => and) *)
(*         l. *)

(*     Definition completion_ll (ll : list (list L.t)) : Prop := *)
(*       (fix ll_interp ll := *)
(*         match ll with *)
(*           | nil => True *)
(*           | c::q => *)
(*             ((fix l_interp c := *)
(*               match c with *)
(*                 | nil => False *)
(*                 | l::q => completion l \/ (l_interp q) *)
(*               end) c) /\ (ll_interp q) *)
(*         end) ll. *)
    
(*     Corollary completion_unfold : *)
(*       forall l,  completion l = *)
(*         if l \in M then True *)
(*           else if L.mk_not l \in M then False *)
(*             else *)
(*               if L.is_proxy l then completion_ll (L.expand l) *)
(*                 else l <<< (L.mk_not l). *)
(*     Proof. *)
(*       intro l; unfold completion at 1. *)
(*       rewrite expand_induction_unfold. *)
(*       destruct (mem l M); auto. *)
(*     Qed. *)

(*     Lemma extends_model : forall l, l \In M -> completion l. *)
(*     Proof. *)
(*       intros l Hl; rewrite completion_unfold. *)
(*       rewrite (mem_1 Hl); exact I. *)
(*     Qed. *)

(*     Remark and_equiv : forall A A' B B', *)
(*       (A <-> A') -> (B <-> B') -> (A /\ B <-> A' /\ B'). *)
(*     Proof. intuition. Qed. *)
(*     Remark or_equiv : forall A A' B B', *)
(*       (A <-> A') -> (B <-> B') -> (A \/ B <-> A' \/ B'). *)
(*     Proof. intuition. Qed. *)
      
(*     Lemma completion_m : S.morphism completion. *)
(*     Proof. *)
(*       intro l; pattern l. *)
(*       apply Wf.well_founded_induction with (R := Llt); clear. *)
(*       exact Llt_wf. *)
(*       unfold S.morphism; intros l IH l' Heq; rewrite 2!completion_unfold. *)
(*       case_eq (mem l M); intro Hl; rewrite Heq in Hl; rewrite Hl. *)
(*       split; auto. *)
(*       case_eq (mem (L.mk_not l) M); intro Hnotl; *)
(*         rewrite L.mk_not_compat in Heq; rewrite Heq in Hnotl; rewrite Hnotl. *)
(*       split; auto. *)
(*       rewrite <- L.mk_not_compat in Heq. *)
(*       assert (Hleq := L.expand_compat l l' Heq). *)
(*       assert (Hllt := Llt_expand l). *)
(*       assert (Hp := L.is_proxy_m l l' Heq). *)
(*       destruct (L.is_proxy l); destruct (L.is_proxy l'). *)

(*       revert Hllt Hleq; generalize (L.expand l'); generalize (L.expand l). *)
(*       intro ll; induction ll; intro ll'; destruct ll'; intros Hllt Hleq. *)
(*       tauto. inversion Hleq. inversion Hleq. *)
(*       inversion Hleq; subst; simpl; apply and_equiv. *)
(*       (* -- *) *)
(*       assert (Hlt : forall y, List.In y a -> Llt y l). *)
(*       intros; apply Hllt with a; intuition. *)
(*       clear H4 Hleq Hllt ll' ll IHll Hl Hnotl Heq l'. *)
(*       revert a l0 H2 Hlt; induction a; destruct l0; intros Hleq Hlt. *)
(*       split; auto. inversion Hleq. inversion Hleq. *)
(*       inversion Hleq; subst; apply or_equiv. *)
(*       apply IH; intuition. *)
(*       apply IHa; intuition. *)
(*       (* -- *) *)
(*       rewrite (IHll ll'); try tauto. *)
(*       intros c y Hcy; apply Hllt; constructor 2; assumption. *)
      
(*       discriminate Hp. discriminate Hp. *)
(*       generalize Heq; rewrite L.mk_not_compat in Heq; generalize Heq; clear. *)
(*       intros; split; order. *)
(*     Qed. *)

(*     Lemma completion_true : S.wf_true completion. *)
(*     Proof. *)
(*       unfold S.wf_true; rewrite completion_unfold.     *)
(*       rewrite (mem_1 Mtrue); simpl; trivial. *)
(*     Qed. *)
    
(*     Lemma completion_expand : S.wf_expand completion. *)
(*     Proof. *)
(*       unfold S.wf_expand; intros l Hl c Hc. *)
(*       rewrite completion_unfold in Hl. *)
(*       case_eq (mem l M); case_eq (mem (L.mk_not l) M);  *)
(*         intros Hnl Hinl; rewrite Hinl,?Hnl in Hl. *)
(*       contradiction (Mwf l (mem_2 Hinl) (mem_2 Hnl)). *)
(*       destruct (Mexpand l (mem_2 Hinl) c Hc) as [x [Hx Hx']]. *)
(*       exists x; split; [exact Hx | exact (extends_model _ Hx')]. *)
(*       contradiction. *)
(*       assert (Hp := L.is_proxy_nil l). *)
(*       destruct (L.is_proxy l).  *)
(*       clear Hnl Hinl; revert Hl c Hc. *)
(*       generalize (L.expand l); clear Hp l; induction l; simpl; intuition. *)
(*       subst. revert c H; clear; induction c; intuition. *)
(*       exists a; intuition. *)
(*       destruct H as [x Hx]; exists x; intuition. *)
(*       rewrite Hp in Hc; auto. inversion Hc. *)
(*     Qed. *)
  
(*     Lemma completion_full_consistent :  *)
(*       forall l, ~~(completion l <-> ~(completion (L.mk_not l))). *)
(*     Proof. *)
(*       intros l; pattern l. *)
(*       apply Wf.well_founded_induction with (R := Llt); clear l. *)
(*       exact Llt_wf. *)
(*       intros l IH N; rewrite 2!completion_unfold in N. *)
(*       case_eq (mem l M); case_eq (mem (L.mk_not l) M);  *)
(*         intros Hnotl Hl; rewrite Hl,Hnotl in N. *)
(*       exact (Mwf l (mem_2 Hl) (mem_2 Hnotl)). *)
(*       rewrite <- (L.mk_not_invol l) in Hl; rewrite Hl in N; apply N; tauto. *)
(*       apply N; tauto. *)
(*       rewrite <- (L.mk_not_invol l) in Hl; rewrite Hl in N. *)
(*       assert (HH := L.expand_mk_not completion completion_m l). *)
(*       assert (contr := L.is_proxy_mk_not l). *)
(*       assert (Hlt := Llt_expand l). *)
(*       assert (Hlt' := Llt_expand (L.mk_not l)). *)
(*       unfold Llt in Hlt, Hlt'; rewrite (L.size_mk_not l) in Hlt'. *)
(*       destruct (L.is_proxy l); destruct (L.is_proxy (L.mk_not l)). *)
(*       apply HH. auto. *)
(*       intros k c Hk Hc; intro Nk. *)
(*       exact (IH k (Hlt c k Hk Hc) Nk). *)
(*       exact N. *)
(*       discriminate contr. *)
(*       discriminate contr. *)
(*       apply N; clear. *)
(*       assert (Hl := L.mk_not_invol l). split; order. *)
(*       assert (Hneq := L.mk_not_fix l). *)
(*       destruct (compare_dec l (L.mk_not l)); tauto. *)
(*     Qed. *)
    
(*     Lemma completion_full : S.full completion. *)
(*     Proof. *)
(*       unfold S.full; intros. *)
(*       generalize (completion_full_consistent l). *)
(*       tauto. *)
(*     Qed. *)
    
(*     Lemma completion_wf : S.consistent completion. *)
(*     Proof. *)
(*       unfold S.consistent; intros. *)
(*       generalize (completion_full_consistent l). *)
(*       tauto. *)
(*     Qed. *)
    
(*     Definition completion_model : S.model := *)
(*       S.mk_model completion *)
(*       completion_full completion_wf  *)
(*       completion_m completion_true completion_expand. *)
(*     Theorem completion_extends : S.submodel M completion_model. *)
(*     Proof. *)
(*       exact extends_model. *)
(*     Qed. *)

(*   End Completion. *)

End SemFacts.
