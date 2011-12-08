Require Import Cnf Semantics.

Set Implicit Arguments.
Unset Strict Implicit.

Global Set Automatic Coercions Import.
  
Inductive Exception (A : Type) := 
| Normal (env : A)
| Inconsistent.
Implicit Arguments Inconsistent [[A]].
Implicit Arguments Normal [[A]].

Module Type ENV_INTERFACE (Import F : CNF).
  Parameter t : Type.

  Parameter Inline empty : t.
  Parameter Inline assume : F.L.t -> t -> Exception t.

  Parameter Inline query : F.L.t -> t -> bool.
  Notation "e |= l" := (query l e = true) (no associativity, at level 50).

  (** Specification *)
  Parameter assumed : t -> F.lset.
  Notation "'dom' t" := (assumed t) (at level 0).

  Axiom assumed_empty : assumed empty [=] singleton L.ltrue.
  Axiom assumed_assume : forall e l E, 
    assume l e = Normal E -> assumed E [=] {l; assumed e}.
  Axiom assumed_inconsistent : forall e l,
    assume l e = Inconsistent -> e |= L.mk_not l.

  Declare Instance query_m : 
    Proper (_eq ==> @Logic.eq t ==> @Logic.eq bool) query.

  Axiom query_true : forall e l, e |= l -> 
    (forall M, Sem.submodel (dom e) M -> M l).
  Axiom query_assumed : forall e l, l \In dom e -> e |= l. 
  Axiom query_monotonic : 
    forall e e' l, dom e [<=] dom e' -> e |= l -> e' |= l.
  Axiom query_expand : 
    forall e l, F.L.is_proxy l = true -> e |= l -> l \In dom e.
(*   Axiom query_consistent :  *)
(*     forall e l, e |= l -> e |= L.mk_not l -> False. *)

  Hint Resolve query_monotonic query_assumed (* query_consistent *).

(*   (** Completion *) *)
(*   Section Completion. *)
(*     Parameter completion_model :  *)
(*       forall (M : t) *)
(*         (Mwf : forall l, l \In dom M -> L.mk_not l \In dom M -> False) *)
(*         (Mtrue : L.ltrue \In dom M) *)
(*         (Mexpand : forall l, l \In dom M -> *)
(*           (forall c, List.In c (L.expand l) ->  *)
(*             exists y, List.In y c /\ M |= y)), Sem.model. *)
    
(*     Axiom completion_extends :  *)
(*       forall M Mwf Mtrue Mexpand,  *)
(*         forall l, M |= l -> @completion_model M Mwf Mtrue Mexpand l. *)
(*   End Completion. *)
End ENV_INTERFACE.

Module ENV (Import F : CNF) <: ENV_INTERFACE F.
  Record t_ := Build_t {
    this :> lset;
    wf : forall l, In l this -> In (L.mk_not l) this -> False
  }.
  Definition t := t_.

  Module SemF := SemFacts F.L Sem.

  Property wf_empty :
    forall l, In l {L.ltrue} -> In (L.mk_not l) {L.ltrue} -> False.
  Proof.
    intros l; set_iff; intros Hl Hnotl.
    apply (L.mk_not_fix l); order.
  Qed.
(*   Property wf_empty :  *)
(*     forall l, In l {} -> In (L.mk_not l) {} -> False. *)
(*   Proof.  *)
(*     intros l; set_iff; tauto. *)
(*   Qed. *)

  Definition empty : t := Build_t wf_empty.

  Property wf_add : 
    forall l (e : t), L.mk_not l \in e = false ->
      forall k, In k {l; e} -> In (L.mk_not k) {l; e} -> False.
  Proof.
    intros l e H k; rewrite !add_iff; intuition.
    apply (L.mk_not_fix k); order.
    rewrite H2 in H; rewrite (mem_1 H0) in H; discriminate.
    rewrite <- (L.mk_not_invol l), <- L.mk_not_compat in H0.
    rewrite H0 in H; rewrite (mem_1 H2) in H; discriminate.
    exact (wf H2 H0).
  Qed.
  Definition assume (l : L.t) (e : t) : Exception t :=
    match L.mk_not l \in e as Hin 
      return L.mk_not l \in e = Hin -> Exception t with
      | true => fun _ => Inconsistent
      | false => fun Hin => Normal (Build_t (wf_add Hin))
    end (refl_equal _).

  Definition query (l : L.t) (e : t) := l \in e.

  (** Specification *)
  Definition assumed (e : t) : lset := this e.

  Property assumed_empty : assumed empty [=] singleton L.ltrue.
  Proof. reflexivity. Qed.

  Property assumed_assume : forall e l E, assume l e = Normal E ->  
    assumed E [=] {l; assumed e}.
  Proof.
    intros; unfold assume in *.
    set (Z := @wf_add l e) in *; clearbody Z.
    destruct (In_dec e (L.mk_not l)).
    discriminate.
    inversion H; subst; reflexivity.
  Qed.

  Property assumed_inconsistent : forall e l,
    assume l e = Inconsistent -> query (L.mk_not l) e = true.
  Proof.
    intros e l; unfold assume, query.
    set (Z := @wf_add l e) in *; clearbody Z.
    destruct (In_dec e (L.mk_not l)); congruence.
  Qed.

  Instance query_m : 
    Proper (_eq ==> @Logic.eq t ==> @Logic.eq bool) query.
  Proof. repeat intro; unfold query; rewrite H; congruence. Qed.

  Property query_true : forall (e : t) l, query l e = true ->
    (forall M, Sem.submodel (assumed e) M -> M l).
  Proof.
    intros e l; unfold query, assumed; destruct (In_dec e l).
    intuition.
    intro; discriminate.
  Qed.

  Property query_assumed : forall e l, l \In assumed e -> query l e = true.
  Proof. intros; unfold query, assumed in *; intuition. Qed.

  Property query_monotonic :
    forall e e' l, assumed e [<=] assumed e' -> 
      query l e = true -> query l e' = true.
  Proof.
    intros; unfold query, assumed in *; intuition.
  Qed.

  Property query_expand : forall (e : t) l, 
    L.is_proxy l = true -> query l e = true -> l \In assumed e.
  Proof. intuition. Qed.

(*   Property query_consistent :  *)
(*     forall (e : t) l, query l e = true -> query (L.mk_not l) e = true -> False. *)
(*   Proof. *)
(*     intros e l; unfold query; intros H1 H2. *)
(*     apply (@wf e) with l; apply mem_2; assumption. *)
(*   Qed. *)
    
(*   (** ** Completion of a well-formed partial assignment *) *)
(*   Section Completion. *)
(*     Unset Implicit Arguments. *)

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
(*       induction a; simpl; intros; omega. *)
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
(*         apply Hlift. *)
(*         generalize (@Llt_expand l); generalize (L.expand l); *)
(*           intro ll; induction ll; intros Hlt. *)
(*         exact Hlnil. *)
(*         refine (@Hlcons a ll _ (IHll _)). *)
(*         assert (Ha := fun y => Hlt a y (or_introl _ (refl_equal a))). *)
(*         clear Hlt; revert a Ha; induction a; intros Hlt. *)
(*         exact Hnil. *)
(*         refine (@Hcons a a0 (IHl a _) (IHa _)). *)
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
    
(*     Variable M : t. *)
(*     Hypothesis Mwf : forall l, l \In M -> (L.mk_not l) \In M -> False. *)
(*     Hypothesis Mtrue : L.ltrue \In M. *)
(*     Hypothesis Mexpand : forall l, l \In M -> *)
(*       (forall c, List.In c (L.expand l) -> exists y, List.In y c /\  *)
(*         y \in M = true). *)
    
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

(*     Remark and_equiv : forall A A' B B', *)
(*       (A <-> A') -> (B <-> B') -> (A /\ B <-> A' /\ B'). *)
(*     Proof. intuition. Qed. *)
(*     Remark or_equiv : forall A A' B B', *)
(*       (A <-> A') -> (B <-> B') -> (A \/ B <-> A' \/ B'). *)
(*     Proof. intuition. Qed. *)
      
(*     Lemma completion_m :  *)
(*       forall l l', l === l' -> (completion l <-> completion l'). *)
(*     Proof. *)
(*       intro l; pattern l. *)
(*       apply Wf.well_founded_induction with (R := Llt); clear. *)
(*       exact Llt_wf. *)
(*       intros l IH l' Heq; rewrite 2!completion_unfold. *)
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

(*     Lemma completion_true : completion L.ltrue. *)
(*     Proof. *)
(*       rewrite completion_unfold. *)
(*       rewrite (mem_1 Mtrue); simpl; trivial. *)
(*     Qed. *)

(*     Lemma extends_model : forall l, l \in M = true -> completion l. *)
(*     Proof. *)
(*       intros l Hl; rewrite completion_unfold. *)
(*       unfold query in Hl; simpl in Hl; rewrite Hl; trivial. *)
(*     Qed. *)
    
(*     Lemma completion_expand :  *)
(*       forall l, completion l ->  *)
(*         (forall c, List.In c (L.expand l) ->  *)
(*           exists l', List.In l' c /\ completion l'). *)
(*     Proof. *)
(*       intros l Hl c Hc. *)
(*       rewrite completion_unfold in Hl. *)
(*       case_eq (mem l M); case_eq (mem (L.mk_not l) M); *)
(*         intros Hnl Hinl; rewrite Hinl,?Hnl in Hl. *)
(*       contradiction (Mwf l (mem_2 Hinl) (mem_2 Hnl)). *)
(*       destruct (Mexpand l (mem_2 Hinl) c Hc) as [x [Hx Hx']]. *)
(*       exists x; split; [exact Hx | exact (extends_model _ Hx')]. *)
(*       contradiction. *)
(*       assert (Hp := L.is_proxy_nil l). *)
(*       destruct (L.is_proxy l). *)
(*       clear Hnl Hinl; revert Hl c Hc. *)
(*       generalize (L.expand l); clear Hp l; induction l; simpl; intuition. *)
(*       subst. revert c H; clear; induction c; intuition. *)
(*       exists a; intuition. *)
(*       destruct H as [x Hx]; exists x; intuition. *)
(*       rewrite Hp in Hc; auto. inversion Hc. *)
(*     Qed. *)
  
(*     Lemma completion_full_consistent : *)
(*       forall l, ~~(completion l <-> ~(completion (L.mk_not l))). *)
(*     Proof. *)
(*       intros l; pattern l. *)
(*       apply Wf.well_founded_induction with (R := Llt); clear l. *)
(*       exact Llt_wf. *)
(*       intros l IH N; rewrite 2!completion_unfold in N. *)
(*       case_eq (mem l M); case_eq (mem (L.mk_not l) M); *)
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
    
(*     Lemma completion_full :  *)
(*       forall l, ~~(~(completion l) -> completion (L.mk_not l)). *)
(*     Proof. *)
(*       intros; generalize (completion_full_consistent l). *)
(*       tauto. *)
(*     Qed. *)
    
(*     Lemma completion_wf : forall l, completion l -> ~(completion (L.mk_not l)). *)
(*     Proof. *)
(*       intros; generalize (completion_full_consistent l). *)
(*       tauto. *)
(*     Qed. *)
    
(*     Definition completion_model : Sem.model := *)
(*       Sem.model_of completion *)
(*       completion_full completion_wf *)
(*       completion_m completion_true completion_expand. *)
(*     Theorem completion_extends :  *)
(*       forall l, query l M = true -> completion_model l. *)
(*     Proof. *)
(*       intros l Hl; unfold completion_model; rewrite Sem.model_as_model_of. *)
(*       apply extends_model. exact Hl. *)
(*     Qed. *)

(*   End Completion. *)
End ENV.

Module EnvFacts (F : CNF)(Import E : ENV_INTERFACE F).
  Property query_m : 
    forall e e' l, dom e [=] dom e' -> (e |= l <-> e' |= l).
  Proof.
    intros e e' l Hdom; split; eapply query_monotonic;
      rewrite Hdom; reflexivity.
  Qed.

  Property query_assume : forall e l l' E, assume l e = Normal E ->
    l === l' -> E |= l'.
  Proof.
    intros; apply query_assumed; rewrite (assumed_assume H).
    apply add_1; auto.
  Qed.

  Property assumed_singleton : 
    forall l E, assume l empty = Normal E -> dom E [=] {l; {F.L.ltrue; {}}}.
  Proof.
    intros l E H a; rewrite (assumed_assume H), add_iff, assumed_empty.
    set_iff; intuition.
  Qed.
End EnvFacts.