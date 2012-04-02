Require Import Term TermUtils DiagProd Counting.
Require Import Sets FoldProps Env Theory.
Require Import Bool. Open Scope bool_scope.
Require Import Uf Use Diff.
Require Import SemLazy LLazy.
Import SEMLAZY.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Inductive input : Set :=
| Equation (a b : term)
| Disequation (a b : term).
Definition input_to_lit (i : input) : LLAZY.t :=
  match i with
    | Equation a b => equation a b
    | Disequation a b => disequation a b
  end.
Inductive submodel_eq (M : model) : list input -> Prop :=
| submodel_nil : submodel_eq M nil
| submodel_cons_eq : 
  forall q a b, M |= a = b ->
    submodel_eq M q -> submodel_eq M ((Equation a b)::q)
| submodel_cons_neq : 
  forall q a b, M |= a <> b ->
    submodel_eq M q -> submodel_eq M ((Disequation a b)::q).
Lemma submodel_eq_In :
  forall M l i, submodel_eq M l -> List.In i l -> M (input_to_lit i).
Proof.
  intros M l i H; induction H; intro; inversion_clear 0; subst; auto.
Qed.

Definition myType := Type.
Module Type CCX_SIG.
  Parameter t : myType.

  Parameter empty : t.
  Parameter assume : input -> t -> Exception t.
  Parameter query : input -> t -> bool.

  Parameter assumed : t -> list input.

  Module Specs.
    Axiom assumed_empty : assumed empty = nil.
    Axiom assumed_assume :
      forall c i c', assume i c = Normal c' -> assumed c' = i::(assumed c).
    Axiom assumed_inconsistent : 
      forall c i, assume i c = Inconsistent -> 
        query (match i with 
                 | Equation a b => Disequation a b
                 | Disequation a b => Equation a b 
               end) c = true.
    
    Axiom query_true : forall c i, query i c = true ->
      forall M, submodel_eq M (assumed c) -> M (input_to_lit i).
    Axiom query_assumed : forall c i, 
      List.In i (assumed c) -> query i c = true.
  End Specs.
End CCX_SIG.
Module Type THEORY.
  Declare Instance Th : Theory.
  Declare Instance ThSpecs : TheorySpecs Th.
End THEORY.

Close Scope Qc_scope.
Module RAWCCX (Import T : THEORY).
  Structure t_ : myType := mk_env {
    G : Use.t;
    D : Uf.t;
    N : Diff.t (term:=term);
    F : list (term * term);
    I : list input
  }.
  Definition t := t_.

  Definition empty := mk_env Use.empty Uf.empty Diff.empty nil nil.

  Definition lleaves (D : Uf.t) (la : list term) : list R :=
    match List.fold_left (fun ll a => List.app (leaves (D a)) ll) la nil with
      | nil => one::nil
      | l => l
    end.

  Fixpoint lcongr (D : Uf.t) (la lb : list term) : bool :=
    match la, lb with
      | nil, nil => true
      | a::qa, b::qb => if D a == D b then lcongr D qa qb else false
      | _, _ => false
    end.

  Definition find_congr_equations1 (D' : Uf.t) (usep : set term) acc :=
    fold (fun u acc =>
      let 'app fu lu := u in
        fold (fun v acc =>
          let 'app fv lv := v in
            if (fu == fv) &&& lcongr D' lu lv then
              (u,v)::acc
            else 
              acc) usep acc
    ) usep acc.

  Definition inter_leaves (D' : Uf.t) (G : Use.t) (t : term) :=
    match leaves (D' t) with
      | nil => (* tous les termes, est safe mais ne doit pas arriver *)
        Use.terms_of G
      | r::q =>
        List.fold_left (fun cand r => inter cand (G r)) q (G r)
    end.

  Definition find_congr_equations2 (D' : Uf.t) (G : Use.t)
    (usep : set term) (touched : list term) acc :=
    (* touchés : liste des t tels que D(t) <> D'(t)
       donc, inclus dans les t tels que p est une feuille de D(t).
       si D(t)=D'(t) et p est une feuille de D(t) v est dans G(p)
       et on l'a dans les premiers cas, donc les touchés sont suffisants.       
       *)
    (* pour chaque t touché, de feuilles L(t),
       pour chaque v qui utilise toutes les feuilles de L(t) 
       pour chaque u dans usep,
       ajouter u = v si nécessaire *)
    List.fold_left (fun acc t =>
      let candidates := inter_leaves D' G t in
        fold (fun v acc =>
          let 'app fv lv := v in
          fold (fun u acc => 
            let 'app fu lu := u in
              if (fu == fv) &&& lcongr D' lu lv then
                (u,v)::acc
              else 
                acc) usep acc
        ) candidates acc
    ) touched acc.

  Definition find_congr_equations 
    (D' : Uf.t) (G : Use.t) (F : list (term * term))
    (p : R) (touched : list term) :=
    let usep := G p in
    let eqs1 := find_congr_equations1 D' usep F in
      find_congr_equations2 D' G usep touched eqs1.

  (** Coherence test is used after the union find has been changed
     in order to test if new equal terms were supposed to be different. *)
  Fixpoint lexists (A : Type) (f : A -> bool) (l:list A) {struct l} : bool :=
    match l with
      | nil => false
      | a::l => if f a then true else lexists f l
    end.
  Definition incoherent (D : Uf.t) (N : Diff.t (term:=term))
    (touched : list term) : bool :=
    lexists (fun t => exists_ (fun u => D t == D u) (Diff.neqs N t)) touched.

  Definition merge (a b : term) (e : t) : Exception t :=
    let 'mk_env G D N F I := e in
    if N a b then Inconsistent
    else
      let ra := D a in
      let rb := D b in
      if ra == rb then Normal e 
      else 
        match solve ra rb with
          | Unsolvable => Inconsistent
          | Solved => Normal e
          | Subst p P => 
            let '(D', touched) := Uf.merge' D p P in
            if incoherent D' N touched then
              Inconsistent
            else
              let G' := Use.merge G p P in
              let F' := find_congr_equations D' G  F p touched in
              Normal (mk_env G' D' N F' I)
        end.

  Definition diff (a b : term) (e : t) : Exception t :=
    if D e a == D e b then 
      Inconsistent 
    else
      Normal {| G := G e; D := D e; 
        N := Diff.separate (N e) a b; F := F e; I := I e|}.

  Definition find_add_equations (G : Use.t) (D : Uf.t) (F : list (term * term))
    (fa : term) (lvs : list R) : list (term * term) :=
    let 'app f la := fa in
    let candidates := Use.using_all G lvs in
      fold (fun t acc => 
        let 'app fb lb := t in
          if (f == fb) &&& lcongr D la lb then
            (fa,t)::acc
          else 
            acc) candidates F.
 
  Nested Fixpoint add_term (fa : term) (e : t) : t :=
    if Uf.mem (D e) fa then e else
      let 'app f la := fa in
        match add_terms la e with
          | mk_env G D N F I =>
            let D' := Uf.add D fa in
            let lvs := lleaves D la in
            let G' := Use.add G fa lvs in
            let F' := find_add_equations G D F fa lvs in
              mk_env G' D' N F' I
        end
    with add_terms (la : list term) (e : t) : t :=
      match la with
        | nil => e
        | a::qa => add_term a (add_terms qa e)
      end.

  Section CleanUp. (* cleaning up pending equations *)
    (** In this section we prove some results in order
       to prove the termination of the [cleanup] functions
       which deals with pending equations until they have
       all been dispatched. *)

    (** An interesting set of terms of a CC environment is 
       the set of terms in the pending equations and in the
       use structure. It is the set of terms with which
       new equations can be built before another [add] is 
       performed. *)
    Fixpoint terms_of_list (l : list (term * term)) : set term :=
      match l with
        | nil => {}
        | (a,b)::l => {a; {b; terms_of_list l}}
      end.
    Definition terms_of (e : t) :=
      Use.terms_of (G e) ++ terms_of_list (F e).

    (** When new equations are found after a merge, they
       are between terms from the use structure. We prove
       a few lemmas before establishing this fact. *)
    Lemma find_congr_equations1_terms :
      forall T D usep acc,
        terms_of_list acc [<=] T -> usep [<=] T ->
        terms_of_list (find_congr_equations1 D usep acc) [<=] T.
    Proof.
      intros; unfold find_congr_equations1.
      apply SetFoldInd.fold_ind2 with (P := fun f => terms_of_list f [<=] T).
      assumption.
      intros; simpl; destruct e as [fu lu].
      apply SetFoldInd.fold_ind2 with (P := fun f => terms_of_list f [<=] T).
      assumption.
      intros; simpl; destruct e as [fv lv].
      destruct (fu == fv); auto.
      destruct (lcongr D0 lu lv); auto.
      simpl; intro e; rewrite 2add_iff; intros [He|[He|He]]; auto;
        apply H0; rewrite <- He; auto.
    Qed.
    Lemma inter_leaves_terms : 
      forall T D G t, Use.terms_of G [<=] T -> inter_leaves D G t [<=] T.
    Proof.
      intros; unfold inter_leaves; simpl.
      destruct (leaves (D0 t0)).
      assumption.
      assert (Hacc : G0 r [<=] T).
      transitivity (Use.terms_of G0); auto.
      apply Use.terms_of_find.
      revert Hacc.
      generalize (G0 r); induction l; simpl; intros.
      assumption.
      apply IHl.
      transitivity s; auto; apply SetProperties.inter_subset_1.
    Qed.
    Lemma find_congr_equations2_terms :
      forall T D G usep touched acc,
        usep [<=] T -> terms_of_list acc [<=] T ->
        Use.terms_of G [<=] T -> 
        terms_of_list (find_congr_equations2 D G usep touched acc) [<=] T.
    Proof.
      intros; unfold find_congr_equations2; revert acc H0.
      induction touched; simpl; intros acc Hacc.
      assumption.
      apply IHtouched; clear IHtouched.
      assert (Hi := @inter_leaves_terms T D0 G0 a H1); revert Hi.
      generalize (inter_leaves D0 G0 a) as s; intros s Hs.
      apply SetFoldInd.fold_ind2 with
        (P := fun f => terms_of_list f [<=] T); simpl; intros.
      assumption.
      destruct e as [fv lv].
      apply SetFoldInd.fold_ind2 with
        (P := fun f => terms_of_list f [<=] T); simpl; intros.
      assumption.
      destruct e as [fu lu].
      destruct (eq_dec fu fv); auto.
      destruct (lcongr D0 lu lv); auto.
      simpl; intros z Hz; rewrite 2add_iff in Hz; 
        destruct Hz as [Hz|[Hz|Hz]]; auto; rewrite <- Hz; auto.
    Qed.

    Theorem find_congr_equations_terms : 
      forall D G F p touched,
        terms_of_list (find_congr_equations D G F p touched) [<=]       
        Use.terms_of G ++ terms_of_list F.
    Proof.
      intros; unfold find_congr_equations.
      apply find_congr_equations2_terms.
      intros a Ha; apply union_2; exact (Use.terms_of_find Ha).
      apply find_congr_equations1_terms.
      apply SetProperties.union_subset_2.
      intros a Ha; apply union_2; exact (Use.terms_of_find Ha).
      apply SetProperties.union_subset_1.
    Qed.

    (* A measure to prove the termination of clean_up :
       * the number of different pairs of terms in the
       [terms_of] the environment. It decreases strictly 
       when merging non-equal terms, and remains unchanged
       otherwise.
       * the number of pending equations, it can increase
       but only if the number of classes has decreased
       *)
    Definition uncongr (D : Uf.t) := fun ab =>
      let 'pair a b := ab in if D a == D b then false else true.
    Definition num_distinct_pairs (e : t) :=
      let pairs := diagProd (terms_of e) in
      let distinct := filter (uncongr (D e)) pairs in
      cardinal distinct.
    Definition num_pending (e : t) :=
      List.length (F e).
    Inductive t_lt (e e' : t) : Prop :=
    | t_lt_1 : num_distinct_pairs e < num_distinct_pairs e' -> t_lt e e'
    | t_lt_2 : num_distinct_pairs e = num_distinct_pairs e' -> 
      num_pending e < num_pending e' -> t_lt e e'.

    Instance uncongr_m (D : Uf.t): Proper (_eq ==> @Logic.eq bool) (uncongr D).
    Proof.
      repeat intro; destruct x; destruct y; inversion H; subst.
      rewrite H3, H5; reflexivity.
    Qed.
    Property num_distinct_pairs_le :
      forall G D N F I u v,
        num_distinct_pairs (mk_env G D N F I) <=
        num_distinct_pairs (mk_env G D N ((u,v)::F) I).
    Proof.
      intros; apply SetProperties.subset_cardinal.
      apply filter_s_m; [apply uncongr_m |].
      apply diagProd_subset_m; unfold terms_of; simpl.
      apply SetProperties.union_subset_5; simpl; intuition.
    Qed.
    Property filter_subset_gen : 
      forall (D D' : Uf.t) s s', 
        (forall a, uncongr D a = true -> uncongr D' a = true) ->
        s [<=] s' -> filter (uncongr D) s [<=] filter (uncongr D') s'.
    Proof.
      intros D0 D1 S0 S1 HD HS; intros a Ha; apply filter_3.
      apply uncongr_m.
      exact (HS _ (filter_1 Ha)).
      exact (HD _ (filter_2 Ha)).
    Qed.
    Property uncongr_gen :
      forall D p P a, uncongr (fst (Uf.merge' D p P)) a = true ->
        uncongr D a = true.
    Proof.
      intros D0 p P [x y]; simpl.
      assert (Hx := Uf.merge'_find D0 p P x).
      assert (Hy := Uf.merge'_find D0 p P y).
      destruct (eq_dec (D0 x) (D0 y)); intro; auto.
      rewrite H in *.
      destruct (eq_dec (fst (Uf.merge' D0 p P) x)
        (fst (Uf.merge' D0 p P) y)); try discriminate; order.
    Qed.

    Theorem merge_decreases : 
      forall e u v e', merge u v e = Normal e' -> 
        t_lt e' (mk_env (G e) (D e) (N e) ((u,v)::(F e)) (I e)).
    Proof.
      intros; destruct e; simpl in *; subst.
      destruct (N0 u v); try discriminate.
      destruct (eq_dec (D0 u) (D0 v)).
      inversion_clear H.
      assert (Hle := num_distinct_pairs_le G0 D0 N0 F0 I0 u v).
      destruct (le_lt_or_eq _ _ Hle) as [Hlt|Heq].
      constructor 1; auto.
      constructor 2; simpl; auto.
      destruct (solve_dec (D0 u) (D0 v)).
      assert (Hle := num_distinct_pairs_le G0 D0 N0 F0 I0 u v).
      inversion H; subst.
      destruct (le_lt_or_eq _ _ Hle) as [Hlt|Heq].
      constructor 1; auto.
      constructor 2; auto.
(*       contradiction. *)
      discriminate.
      destruct (Uf.merge' D0 p P) as [D' touched]_eqn:Htouched.
      destruct (incoherent D' N0 touched).
      discriminate.
      inversion_clear H; constructor 1; unfold num_distinct_pairs; simpl.
      assert (Hgen := @uncongr_gen D0 p P).
      rewrite Htouched in Hgen; simpl in Hgen.
      destruct (lt_dec u v) as [Hlt|Hgt].
      apply SetProperties.subset_cardinal_lt with (u, v).
      apply filter_subset_gen; auto.
      apply diagProd_subset_m; unfold terms_of; simpl.
      rewrite Use.terms_of_merge; auto; rewrite find_congr_equations_terms.
      rewrite <- SetProperties.union_assoc; apply union_s_m.
      apply SetProperties.union_subset_3; reflexivity.
      intuition.
      apply filter_3.
      apply uncongr_m.
      rewrite diagProd_iff; repeat split; auto; 
        apply union_3; simpl.
      apply add_1; reflexivity. apply add_2; apply add_1; reflexivity.
      simpl; destruct (eq_dec (D0 u) (D0 v)); auto; order.
      intro abs; assert (abs' := filter_2 abs); clear abs; simpl in abs'.
      destruct (eq_dec (D' u) (D' v)) as [Heq|Hneq]; [discriminate|].
      rewrite <- 2Uf.merge'_find, Htouched in Hsubst; exact (Hneq Hsubst).
      apply SetProperties.subset_cardinal_lt with (v, u).
      apply filter_subset_gen; auto.
      apply diagProd_subset_m; unfold terms_of; simpl.
      rewrite Use.terms_of_merge; auto; rewrite find_congr_equations_terms.
      rewrite <- SetProperties.union_assoc; apply union_s_m.
      apply SetProperties.union_subset_3; reflexivity.
      intuition.
      apply filter_3.
      apply uncongr_m.
      rewrite diagProd_iff; repeat split; try apply union_3; simpl.
      apply add_2; apply add_1; reflexivity. apply add_1; reflexivity. 
      destruct (compare_dec u v); auto; try contradiction.
      contradiction H0; rewrite H; reflexivity.
      simpl; destruct (eq_dec (D0 v) (D0 u)); auto; order.
      intro abs; assert (abs' := filter_2 abs); clear abs; simpl in abs'.
      destruct (eq_dec (D' v) (D' u)) as [Heq|Hneq]; [discriminate|].
      rewrite <- 2Uf.merge'_find, Htouched in Hsubst; apply Hneq; auto.
    Qed.
    Require Import Wf Recdef Lexico.

    (** Finally, our relation is well-founded *)
    Remark num_distincts_wf : 
      well_founded (fun a a' => num_distinct_pairs a < num_distinct_pairs a').
    Proof. 
      apply well_founded_ltof.
    Qed.
    Remark num_pending_wf : 
      well_founded (fun a a' => num_pending a < num_pending a').
    Proof. 
      apply well_founded_ltof.
    Qed.
    Theorem t_lt_wf : well_founded t_lt.
    Proof.
      set (m1 := num_distinct_pairs); set (m2 := num_pending).
      set (ordertt := fun c1 c2 => lex2 (m1 c1, m2 c1) (m1 c2, m2 c2)).
      pose (aux := orderAB _ _ m1 m2).
      pose (rof := fun x y => aux (x,x) (y,y)).
      apply (wf_incl t t_lt ordertt).
      unfold Relation_Definitions.inclusion; intros.
      unfold ordertt; unfold lex2; inversion H; simpl.
      left; assumption. right; split; assumption.
      apply (wf_incl t ordertt rof).
      unfold Relation_Definitions.inclusion; intros.
      unfold rof; unfold aux; unfold orderAB; unfold ordertt in H.
      simpl in *; auto.
      unfold rof.
      apply (wf_inverse_image t (t*t)).
      unfold aux.
      apply wf_lt_lexico.
    Qed.

    Fixpoint guard (n : nat) (wfR : well_founded t_lt) {struct n} : 
      well_founded t_lt :=
      match n with
        | 0 => wfR
        | S n' =>
          fun x => Acc_intro x (fun y _ => guard n' (guard n' wfR) y)
      end.
    Definition guarded_wf_lt := guard 100 t_lt_wf.

    Function clean_up (e : t) {wf t_lt e} : Exception t :=
      let 'mk_env G D N F I := e in
      match F with
        | nil => Normal e
        | (u,v)::F' =>
          match merge u v (mk_env G D N F' I) with
            | Normal e' => clean_up e'
            | Inconsistent => Inconsistent
          end
      end.
    Proof.
      intros; subst; revert teq2; apply merge_decreases.
      exact guarded_wf_lt.
    Defined.
    Global Opaque clean_up.
(*     Definition clean_up (e : t) : Exception t := *)
(*       clean_up_rec e. *)
  End CleanUp.

  Definition assume (i : input) (e : t) :=
    match i with
      | Equation a b =>
        match merge a b (add_term b (add_term a e)) with
          | Normal (mk_env G' D' N' F' I') => 
            clean_up (mk_env G' D' N' F' (i::I'))
          | Inconsistent => Inconsistent
        end
      | Disequation a b =>
        match clean_up (add_term b (add_term a e)) with
          | Normal e' => 
            match diff a b e' with
              | Normal (mk_env G' D' N' F' I') => 
                Normal (mk_env G' D' N' F' (i::I'))
              | Inconsistent => Inconsistent
            end
          | Inconsistent => Inconsistent
        end
    end.

  Definition are_equal (a b : term) (e : t) : bool :=
    match clean_up (add_term b (add_term a e)) with
      | Normal e' => D e' a == D e' b
      | Inconsistent => true
    end.
  Definition are_diff (a b : term) (e : t) : bool :=
    match assume (Equation a b) e with
      | Normal e' => false
      | Inconsistent => true
    end.

  Definition query (q : input) (e : t) : bool :=
    match q with
      | Equation a b => are_equal a b e
      | Disequation a b => are_diff a b e
    end.

  Definition assumed := I.

  Module Specs.
    Ltac simpl_mk_env :=
      simpl mk_env in *;
        simpl D in *; simpl G in *; simpl N in *; simpl F in *; simpl I in *.

    (** The invariant verified by a CC environment includes : 
       - the UF data structure's own invariant
       - the Diff data structures' own invariant
       - the fact that equalites in the UF are consequences
       of the inputs, and at least the equation-inputs have
       been merged
       - the fact that the pending equations are consequences 
       of the inputs
       - the disequations in N are exactly the direct consequences
       of the disequations in the inputs
       - the Diff structure does not contradict the UF, and all
       terms in the Diff structure have been added to the UF
       explicitely.
       The first two conditions are simply subclass components. For
       the 3rd, we need to talk about all the equation that have
       been merged ; we dont compute them but require that they exist
       and are themselves consequences of the equation-inputs 
       (in contrast to the disequations input).
       For the fourth condition, we simply state that equations are
       syntactically justified by congruence + the current UF.
       As for the sixth, the condition on terms guarantees that
       we only need check the incoherence on terms touched in UF.
       *)
    Fixpoint eqns_of (l : list input) : list (term * term) :=
      match l with
        | nil =>  nil
        | (Equation a b)::q => (a, b)::(eqns_of q)
        | _::q => eqns_of q
      end.
    Definition iter l r : option R :=
      match iter l with
        | Some f => Some (f r)
        | None => None
      end.
    Inductive coincides (D : Uf.t) (I : list input) : Prop :=
    | mk_coincides :
      forall eqns,
        (forall p, List.In p (eqns_of I) -> List.In p eqns) ->
        (forall M, models_list M (eqns_of I) -> models_list M eqns) ->
        (forall t, Some (D t) === iter eqns (make t)) ->
        coincides D I.

    Inductive justify (D : Uf.t) : list (term * term) -> Prop :=
    | justify_nil : justify D nil
    | justify_cons :
      forall f lu lv F, lcongr D lu lv = true -> justify D F -> 
        justify D ((app f lu, app f lv)::F).

    Definition Ncoincides (N : Diff.t (term:=term)) (I : list input) : Prop :=
      forall a b, a \In Diff.neqs N b <-> 
        (List.In (Disequation a b) I \/ List.In (Disequation b a) I).

    Definition coherent (D : Uf.t) (N : Diff.t (term:=term)) : Prop :=
      (forall a b, N a b = true -> b \In Uf.range D /\ D a =/= D b).

    Class Wf (cc : t) := {
      Dwf :> Uf.Wf (D cc);
      Nwf :> Diff.Wf (N cc);
      Dcorrect : coincides (D cc) (I cc);
      Fcorrect : justify (D cc) (F cc);
      Ncorrect : Ncoincides (N cc) (I cc);
      coherence : coherent (D cc) (N cc)
    }.
    
    (** Link between [submodel_eq] and [models_list] *)
    Remark submodel_eq_models_list : 
      forall M I, submodel_eq M I -> models_list M (eqns_of I).
    Proof.
      intros M I0; induction I0; intro HM; inversion HM; subst; simpl.
      constructor.
      constructor (auto).
      auto.
    Qed.

    (** justify + coincides means the pending equations are semantical
       consequences of the input equations *)
    Lemma theory_iter_correct : 
      forall E f a, Theory.iter E = Some f -> implyX E a (f a).
    Proof.
      induction E; intros. 
      simpl in H; inversion H; reflexivity.
      simpl in H; destruct a as [t1 t2].
      destruct (Theory.iter E) as [fE|]; try discriminate.
      assert (ISolve := fun E0 p P => @implyX_Solve _ _ E0 p P
        (fE (make t1)) (fE (make t2))).
      destruct (solve_dec (fE (make t1)) (fE (make t2))); inversion H; subst.
      apply implyX_weaken; apply IHE; reflexivity.
      transitivity (fE a0).
      apply implyX_weaken; apply IHE; reflexivity.
      apply implyX_Subst with p P; auto.
      apply ISolve; [|reflexivity].
      transitivity (make t1).
      apply implyX_weaken; symmetry; apply IHE; reflexivity.
      transitivity (make t2).
      apply implyX_Ax; constructor (auto).
      apply implyX_weaken; apply IHE; reflexivity.
    Qed.

    Lemma iter_correct : forall E a b,
      iter E a === Some b -> implyX E a b.
    Proof.
      intros; unfold iter in *.
      assert (Ht := @theory_iter_correct E).
      destruct (Theory.iter E); inversion H; subst.
      rewrite <- H2; apply Ht; reflexivity.
    Qed.
    Theorem justify_coincides :
      forall D I F,
        coincides D I -> justify D F ->
        forall M, models_list M (eqns_of I) -> models_list M F.
    Proof.
      intros d i f [eqns _ Heqns Hiter] Hj.
      induction Hj; intros M HM; constructor (auto).
      apply models_eq_congr.
      assert (Heqn := Heqns M HM); clear Heqns.
      assert (IHj := IHHj M HM); clear IHHj.
      revert lv H; induction lu; intros; destruct lv; simpl in H.
      constructor.
      discriminate. discriminate.
      destruct (eq_dec (d a) (d t0)); try discriminate H.
      constructor (auto).
      refine (@implyX_entails Th ThSpecs eqns _ _ _ M Heqn).
      apply implyX_Trans with (d a).
      apply iter_correct; rewrite <- Hiter; reflexivity.
      transitivity (d t0).
      rewrite H0; reflexivity.
      apply implyX_Sym; apply iter_correct;
        rewrite <- Hiter; auto.
    Qed.

    (** [coincides] and [Ncoincides] ensure soundness for the
       respective data structures. *)
    Theorem coincides_submodel : 
      forall D I, coincides D I -> 
        forall M a b, submodel_eq M I -> D a === D b -> M |= a = b.
    Proof.
      intros d i [eqns _ Heqns Hiter] M a b Hsub Heq.
      apply implyX_entails with eqns.
      apply implyX_Trans with (d a); [| apply implyX_Trans with (d b)].
      apply iter_correct. rewrite Hiter; reflexivity.
      rewrite Heq; reflexivity.
      apply implyX_Sym; apply iter_correct; rewrite Hiter; reflexivity.
      apply Heqns; generalize Hsub; clear; induction i.
      intros; constructor.
      intro H; inversion_clear H; simpl; auto.
      constructor; auto.
    Qed.
(*     Theorem coincides_submodel' :  *)
(*       forall D I, coincides D I ->  *)
(*         forall M a b, submodel_eq M I -> equivX (D a) (D b) -> M |= a = b. *)
(*     Proof. *)
(*       intros d i [eqns _ Heqns Hiter] M a b Hsub Heq. *)
(*       apply implyX_entails with eqns. *)
(*       apply implyX_Trans with (d a); [| apply implyX_Trans with (d b)]. *)
(*       apply iter_correct. rewrite Hiter; reflexivity. *)
(*       apply implyX_equivX; assumption. (* rewrite Heq; reflexivity. *) *)
(*       apply implyX_Sym; apply iter_correct; rewrite Hiter; reflexivity. *)
(*       apply Heqns; generalize Hsub; clear; induction i. *)
(*       intros; constructor. *)
(*       intro H; inversion_clear H; simpl; auto. *)
(*       constructor; auto. *)
(*     Qed. *)
    
    Theorem Ncoincides_submodel : 
      forall N I, Ncoincides N I -> 
        forall M a b, submodel_eq M I -> N a b = true -> M |= a <> b.
    Proof.
      intros n i HNc M a b Hsub Heq.
      rewrite <- Diff.neqs_iff in Heq.
      rewrite (HNc a b) in Heq; destruct Heq as [H1|H2].
      exact (submodel_eq_In Hsub H1).
      apply models_neq_sym; exact (submodel_eq_In Hsub H2).
    Qed.

    (** [coincides] and [Ncoincides] are also guaranteeing
       some completeness : at least the inputs are handled. *)
    Corollary coincides_inputs :
      forall D I a b, coincides D I -> 
        List.In (Equation a b) I -> D a === D b.
    Proof.
      intros d i a b [eqns HinI _ Hiter] Hin.
      cut (iter eqns (make a) === iter eqns (make b)).
      rewrite <- 2Hiter; intro H; inversion H; auto.
      assert (cut : List.In (a, b) eqns).
      apply HinI; revert Hin; clear; induction i; simpl; auto.
      intros [H|H]. rewrite H; left; auto.
      destruct a0; [right|]; auto.
      revert cut; clear.
      induction eqns.
      intro; contradiction.
      intro H; inversion_clear H; subst; unfold iter in *; simpl in *.
      destruct (Theory.iter eqns) as [f |]_eqn:Hf; [|reflexivity].
      destruct (solve_dec (f (make a)) (f (make b))); try constructor; auto.

      destruct a0 as [x y]; simpl.
      assert (Heq := IHeqns H0); clear IHeqns H0.
      destruct (Theory.iter eqns) as [f |]_eqn:Hf; [|reflexivity].
      destruct (solve_dec (f (make x)) (f (make y))); try constructor; auto.
      inversion Heq; auto.
      inversion Heq; subst; rewrite H1; reflexivity.
    Qed.
(*     Corollary coincides_inputs' : *)
(*       forall D I a b, coincides D I ->  *)
(*         List.In (Equation a b) I -> equivX (D a) (D b). *)
(*     Proof. *)
(*       intros d i a b [eqns HinI _ Hiter] Hin. *)
(*       assert (cut : List.In (a, b) eqns). *)
(*       apply HinI; revert Hin; clear; induction i; simpl; auto. *)
(*       intros [H|H]. rewrite H; left; auto. *)
(*       destruct a0; [right|]; auto. *)
(*       assert (Ax := implyX_Ax (Th:=Th) cut); unfold implyX in Ax. *)
(*       generalize (Hiter a) (Hiter b); unfold iter; intros Ha Hb. *)
(*       destruct (Theory.iter eqns) as [f|]_eqn:Hf. *)
(*       inversion Ha; inversion Hb; subst. *)
(*       rewrite H1, H4; assumption. *)
(*       inversion Ha. *)
(*     Qed. *)

    Corollary Ncoincides_inputs : 
      forall N I a b, Ncoincides N I -> 
        List.In (Disequation a b) I -> N a b = true.
    Proof.
      intros n i a b Hnc Hin.
      rewrite <- Diff.neqs_iff, (Hnc a b); tauto.
    Qed.
  
    (** About [empty] *)
    Property assumed_empty : assumed empty = nil.
    Proof. 
      reflexivity.
    Qed.
    Instance Wf_empty : Wf empty.
    Proof. constructor.
      exact Uf.Wf_empty.
      exact Diff.Wf_empty.
      exists nil; simpl; auto.
      constructor.
      intros a b; simpl; rewrite Diff.neqs_empty, empty_iff; tauto.
      intros a b; rewrite <- Diff.neqs_iff; simpl.
      rewrite Diff.neqs_empty; intro z; contradiction (empty_1 z).
    Qed.
    
    (** About [find_add_equations] *)
    Theorem find_add_equations_correct : 
      forall G D F fa lvs, justify D F -> 
        justify D (find_add_equations G D F fa lvs).
    Proof.
      intros; unfold find_add_equations.
      destruct fa as [f la].
      apply SetFoldInd.fold_ind2.
      assumption.
      intros [fb lb] a He Ha.
      destruct (eq_dec f fb); auto.
      case_eq (lcongr D0 la lb); intros; auto.
      rewrite H0; constructor; auto.
    Qed.
    Theorem find_add_equations_extend : 
      forall G D F fa lvs p,
        List.In p F -> List.In p (find_add_equations G D F fa lvs).
    Proof.
      intros; unfold find_add_equations.
      destruct fa as [f la].
      apply SetFoldInd.fold_ind2.
      assumption.
      intros [fb lb] a He Ha.
      destruct (eq_dec f fb); auto.
      destruct (lcongr D0 la lb); intuition.
    Qed.

    (** About [find_congr_equations] *)
    Lemma find_congr_equations1_correct :
      forall D usep acc, justify D acc ->
        justify D (find_congr_equations1 D usep acc).
    Proof.
      intros; unfold find_congr_equations1.
      apply SetFoldInd.fold_ind2.
      assumption.
      intros [fu lu] a He Ha.
      apply SetFoldInd.fold_ind2.
      assumption.
      intros [fv lv] b He' Hb.
      destruct (eq_dec fu fv); auto.
      case_eq (lcongr D0 lu lv); intros; auto.
      rewrite H0; constructor; auto.
    Qed.
    Theorem find_congr_equations1_extend : 
      forall D usep acc p,
        List.In p acc -> List.In p (find_congr_equations1 D usep acc).
    Proof.
      intros; unfold find_congr_equations1.
      apply SetFoldInd.fold_ind2.
      assumption.
      intros [fu lu] a He Ha.
      apply SetFoldInd.fold_ind2.
      assumption.
      intros [fv lv] b He' Hb.
      destruct (eq_dec fu fv); auto.
      destruct (lcongr D0 lu lv); intuition.
    Qed.

    Lemma find_congr_equations2_correct :
      forall D G usep touched acc, justify D acc ->
        justify D (find_congr_equations2 D G usep touched acc).
    Proof.
      intros; unfold find_congr_equations2.
      revert acc H; induction touched; intros; simpl.
      assumption.
      apply IHtouched; clear IHtouched.
      apply SetFoldInd.fold_ind2.
      assumption.
      intros [fv lv] l He Hl.
      apply SetFoldInd.fold_ind2.
      assumption.
      intros [fu lu] l' He' Hl'.
      destruct (eq_dec fu fv); auto.
      case_eq (lcongr D0 lu lv); intros; auto.
      rewrite H0; constructor; auto.
    Qed.
    Lemma find_congr_equations2_extend :
      forall D G usep touched acc p, List.In p acc ->
        List.In p (find_congr_equations2 D G usep touched acc).
    Proof.
      intros; unfold find_congr_equations2.
      revert acc H; induction touched; intros; simpl.
      assumption.
      apply IHtouched; clear IHtouched.
      apply SetFoldInd.fold_ind2.
      assumption.
      intros [fv lv] l He Hl.
      apply SetFoldInd.fold_ind2.
      assumption.
      intros [fu lu] l' He' Hl'.
      destruct (eq_dec fu fv); auto.
      destruct (lcongr D0 lu lv); intuition.
    Qed.
    
    Theorem find_congr_equations_correct : 
      forall D G F p touched, justify D F ->
        justify D (find_congr_equations D G F p touched).
    Proof.
      intros; unfold find_congr_equations.
      apply find_congr_equations2_correct.
      apply find_congr_equations1_correct.
      assumption.
    Qed.
    Theorem find_congr_equations_extend : 
      forall D G F p touched eqn, List.In eqn F ->
        List.In eqn (find_congr_equations D G F p touched).
    Proof.
      intros; unfold find_congr_equations.
      apply find_congr_equations2_extend.
      apply find_congr_equations1_extend.
      assumption.
    Qed.

    (** Specification of [add_term] and [add_terms]:
       - [add_term b c] returns [c']
       -- [I c' = I c]
       -- [D c'] extends [D c]
       -- [range (D c')] is a superset of [{b; range (D c)}]
       -- [F c'] extends [F c]
       -- [N c' = N c]
       - [add_terms l c] returns [c']
       -- [I c' = I c]
       -- [D c'] extends [D c]
       -- [range (D c')] is a superset of [{range (D c)}]
       -- [F c'] extends [F c]
       -- [N c' = N c]
       *)
    Inductive add_term_spec (b : term) (c : t) : t -> Prop :=
    | add_term_spec_Normal :
      forall G' (D' : Uf.t) F'
        (Hadd_uf : forall x y, D c x === D c y -> D' x === D' y)
        (Hadd_range : {b; Uf.range (D c)} [<=] Uf.range D')
        (Hadd_ext : forall p, List.In p (F c) -> List.In p F'),
        add_term_spec b c (mk_env G' D' (N c) F' (I c)).
    Derive Inversion add_term_spec_inv with
    (forall b c, add_term_spec b c (add_term b c)) Sort Prop.
    Size add_term_spec_inv.

    Inductive add_terms_spec (l : terms) (c : t) : t -> Prop :=
    | add_terms_spec_Normal : 
      forall G' (D' : Uf.t) F'
        (Hadd_uf : forall x y, D c x === D c y -> D' x === D' y)
        (Hadd_range : Uf.range (D c) [<=] Uf.range D')
        (Hadd_ext : forall p, List.In p (F c) -> List.In p F'),
        add_terms_spec l c (mk_env G' D' (N c) F' (I c)).
    
    Opaque find_add_equations.
    Property add_term_terms_dec : 
      (forall a e, add_term_spec a e (add_term a e)) /\
      (forall l e, add_terms_spec l e (add_terms l e)).
    Proof.
      apply term_mutual_ind; intros; simpl.
      destruct (Uf.mem (D e) (app f lt)) as [ ]_eqn:Hmem.
      destruct e; constructor; auto; simpl_mk_env.
      rewrite Uf.range_mem, <- mem_iff in Hmem; intuition.
      fold (add_terms lt e); destruct (H e).
      constructor.
      intros; apply Uf.add_conservative; auto.
      rewrite Uf.range_add; apply add_s_m; auto.
      auto using find_add_equations_extend.
      destruct e; constructor (auto). reflexivity.
      destruct (H0 e).
      destruct (H (mk_env G' D' (N e) F' (I e))).
      simpl; constructor; auto.
      refine (transitivity _ Hadd_range0); intuition.
    Qed.
    Definition add_term_dec := Eval simpl in proj1 (add_term_terms_dec).
    Definition add_terms_dec := Eval simpl in proj2 (add_term_terms_dec).
    Transparent find_add_equations.

    Lemma lcongr_add : forall `{@Uf.Wf Th d} a lu lv,
      lcongr (Uf.add d a) lu lv = lcongr d lu lv.
    Proof.
      intros d dwf a; induction lu; destruct lv; simpl; auto.
      rewrite IHlu.
      assert (Ha := Uf.add_find a a0).
      assert (Ht := Uf.add_find a t0).
      destruct (eq_dec (Uf.add d a a0) (Uf.add d a t0)); 
        destruct (eq_dec (d a0) (d t0)); simpl; auto; order.
    Qed.
    Lemma justify_add : forall `{@Uf.Wf Th d} a F,
      justify (Uf.add d a) F <-> justify d F.
    Proof.
      intros; split; intro J; induction J; simpl in *; constructor (auto).
      rewrite lcongr_add in H0; assumption.
      rewrite lcongr_add; assumption.
    Qed.
    Lemma coincides_add : forall `{@Uf.Wf Th d} a I,
      coincides (Uf.add d a) I <-> coincides d I.
    Proof.
      intros; split; intro J; induction J; simpl in *;
        exists eqns; auto.
      intro z; rewrite <- H2; symmetry; constructor; 
        apply Uf.add_find; auto.
      intro z; rewrite <- H2; constructor; apply Uf.add_find; auto.
    Qed.
    Lemma coherent_add : forall `{@Uf.Wf Th d} a n,
      coherent d n -> coherent (Uf.add d a) n.
    Proof.
      intros; simpl in *; repeat intro.
      destruct (H0 a0 b H1) as [C1 C2]; repeat split.
      rewrite Uf.range_add; apply add_2; exact C1.
      rewrite 2Uf.add_find; auto.
    Qed.

    Property Wf_add_term_terms : 
      (forall a `{Wf e}, Wf (add_term a e)) /\ 
      (forall l `{Wf e}, Wf (add_terms l e)).
    Proof.
      intros; apply term_mutual_ind; intros; simpl.
      destruct (Uf.mem (D e) (app f lt)); auto.
      assert (Hwf := H e H0); clear H H0; fold (add_terms lt e).
      destruct (add_terms_dec lt e); simpl.
      assert (Hj : justify (Uf.add D' (app f lt)) F').
      destruct Hwf; rewrite justify_add; auto.
      apply SetFoldInd.fold_ind2; simpl; intros.
      destruct Hwf; constructor; simpl in *.
      apply Uf.Wf_add.
      assumption.
      rewrite coincides_add; assumption.
      assumption.
      assumption.
      apply coherent_add; assumption.
      destruct Hwf; destruct H0; constructor; simpl in *.
      assumption.
      assumption.
      assumption.
      destruct e0 as [fb lb]; destruct (eq_dec f fb); auto.
      case_eq (lcongr D' lt lb); intros; auto.
      rewrite H0 in *; constructor; auto.
      rewrite lcongr_add; auto.
      assumption.
      assumption.
      assumption.
      apply H; apply H0; assumption.
    Qed.
    
    Instance Wf_add_term : forall (a : term) `{Wf e}, Wf (add_term a e).
    Proof. exact (proj1 (Wf_add_term_terms)). Defined.
    Instance Wf_add_terms : forall (l : terms) `{Wf e}, Wf (add_terms l e).
    Proof. apply (proj2 (Wf_add_term_terms)). Defined.

    Tactic Notation "decide" "add_term" :=
      match goal with
        | |- context f [add_term ?A ?E] =>          
          let wf := fresh "Hwfadd" in
            (assert (wf := @Wf_add_term A E _) || 
              assert (wf := fun w => @Wf_add_term A E w));
          destruct (add_term_dec A E); simpl_mk_env
        | _ => fail 2 "No occurrence of add_term found in the goal."
      end.
    Tactic Notation "decide" "add_term" "in" hyp(H) :=
      match goal with
        | H : context f [add_term ?A ?E] |- _ =>
          let wf := fresh "Hwfadd" in
            (assert (wf := @Wf_add_term A E _) || 
              assert (wf := fun w => @Wf_add_term A E w));
            destruct (add_term_dec A E); simpl_mk_env
        | _ => fail 2 "No occurrence of add_term found in " H
      end.

(*     Fact test1 : forall a e, I e = I (add_term a e). *)
(*     Proof. *)
(*       intros; decide add_term. *)
(*       reflexivity. *)
(*     Defined. *)
(*     Size test1. (* 131 *) *)
(*     Eval cbv iota zeta delta -[Wf_add_term add_term_dec add_term I N] in test1. *)
(*     Print test1. *)
(*     Fact test2 : forall a e, I e = I (add_term a e). *)
(*     Proof. *)
(*       intros. *)
(*       assert (Z := add_term_dec a e). *)
(*       destruct Z; simpl. *)
(*       reflexivity. *)
(*     Defined. *)
(*     Size test2. (* 103 *) *)
(*     Eval cbv iota zeta delta -[Wf_add_term add_term_dec add_term I N] in test2. *)
(*     Print test2. *)
(*     Fact test3 : forall a e, I e = I (add_term a e). *)
(*     Proof. *)
(*       intros. *)
(*       assert (Z := add_term_dec a e). *)
(*       inversion_clear Z. *)
(*       reflexivity. *)
(*     Defined. *)
(*     Size test3. (* 400 *) *)
(*     Eval cbv iota zeta delta -[Wf_add_term add_term_dec add_term  *)
(*       D F N I List.In equiv] in test3. *)
(*     Print test3. *)
(*     Fact test4 : forall a e, I e = I (add_term a e). *)
(*     Proof. *)
(*       intros. *)
(*       assert (Z := add_term_dec a e). *)
(*       induction Z; simpl. *)
(*       reflexivity. *)
(*     Defined. *)
(*     Size test4. (* 103 *) *)
(*     Eval cbv iota zeta delta -[Wf_add_term add_term_dec add_term  *)
(*       D F N I List.In equiv add_term_spec_inv] in test4. *)
(*     Print test4. *)
(*     Check add_term_spec_ind. *)
(*     Check add_term_spec_inv. *)
(*     Fact test5 : forall a e, I e = I (add_term a e). *)
(*     Proof. *)
(*       intros. *)
(*       assert (Z := add_term_dec a e). *)
(*       inversion Z using add_term_spec_inv; simpl; intros. *)
(*       rewrite <- H1; reflexivity. *)
(*     Defined. *)
(*     Size test5. (* 149 *) *)
(*     Print test5. *)

    (** About [incoherent] :
       - if it returns [false], then the environment is coherent 
       - if it returns [true], there is an inconsistence between [N] and [D]
       *)
    Theorem incoherent_false : 
      forall D N touched, incoherent D N touched = false ->
        forall t, List.In t touched -> 
          forall a, N a t = true -> D t =/= D a.
    Proof.
      intros d n; induction touched; unfold incoherent; 
        simpl; intros Hinc x Hx y Hy abs.
      contradiction.
      destruct Hx; subst.
      destruct (@exists_dec _ _ _ _ 
        (Diff.neqs n x) (fun u : term => d x == d u) _).
      discriminate.
      apply Hfalse; exists y; split.
      rewrite Diff.neqs_iff; auto.
      destruct (eq_dec (d x) (d y)); auto; contradiction.
      destruct (@exists_dec _ _ _ _ 
        (Diff.neqs n a) (fun u : term => d a == d u) _).
      discriminate.
      exact (IHtouched Hinc _ H _ Hy abs).
    Qed.
    Theorem incoherent_true : 
      forall D N touched, incoherent D N touched = true ->
        exists t, exists a, N a t = true /\ D t === D a.
    Proof.
      intros d n; induction touched; unfold incoherent; simpl;
        intro Hcoh.
      discriminate Hcoh.
      destruct (@exists_dec _ _ _ _ 
        (Diff.neqs n a) (fun u : term => d a == d u) _).
      destruct Htrue as [b [Hb1 Hb2]].
      exists a; exists b; repeat split.
      rewrite <- Diff.neqs_iff; exact Hb1.
      destruct (eq_dec (d a) (d b)); [assumption | discriminate].
      exact (IHtouched Hcoh).
    Qed.

    Corollary coherent_merge : 
      forall `{Hd: @Uf.Wf Th d} p P `{Hn : @Diff.Wf _ _ n},
        coherent d n -> incoherent (fst (Uf.merge' d p P))
        n (snd (Uf.merge' d p P)) = false ->
        coherent (fst (Uf.merge' d p P)) n.
    Proof.
      intros; intros x y Hxy.
      assert (Htouched := Uf.merge'_touched_spec d p P).
      assert (Hcohxy := fun Hx => incoherent_false H0 Hx Hxy).
      destruct (H _ _ Hxy) as [C1 C2].
      rewrite Diff.is_wf in Hxy.
      assert (Hcohyx := fun Hy => incoherent_false H0 Hy Hxy).
      destruct (H _ _ Hxy) as [D1 D2].
      rewrite !Uf.merge'_find in Hcohxy, Hcohyx |- *.

      assert (Hrange := Uf.range_merge' d p P).
      set (touch := snd (Uf.merge' d p P)) in *; clearbody touch.
      set (D' := fst (Uf.merge' d p P)) in *; clearbody D'.
      repeat split.
      rewrite Hrange; exact C1.
      intro abs.
      destruct (eq_dec (d y) (subst p P (d y))) as [Heqy|Hneqy].
      rewrite <- Heqy in *.
      apply Hcohyx; auto; rewrite Htouched; split.
      rewrite Uf.range_mem; apply mem_1; exact D1.
      intro abs'; rewrite <- abs' in abs; exact (C2 abs).
      apply Hcohxy; auto; rewrite Htouched; split.
      rewrite Uf.range_mem; apply mem_1; exact C1.
      intro; auto.
    Qed.
    
    (** Specification of [merge]:
       - [merge a b c] returns [Normal c']
       -- [I c' = I c]
       -- [Wf] is preserved from [c] to [c'] if [a = b] is itself
          a consequence of the inputs
       -- [D c' a === D c' b]
       -- [D c'] contains [D c]
       -- [Uf.range (D c) [<=] Uf.range D']
       -- [F c'] is an extension of [F c]
       -- [N' c = N c]
       - [merge a b c] returns [Inconsistent]
       -- [forall M, submdel_eq M (I e) -> M |= a <> b]
       *)
    Inductive merge_spec (a b : term) (c : t) : Exception t -> Prop :=
    | merge_spec_Inconsistent :
      forall (Hmerge_inc : 
        Wf c -> forall M, submodel_eq M (I c) -> M |= a = b -> 
          forall x y, M |= x = y),
      merge_spec a b c Inconsistent
    | merge_spec_Normal :
      forall G' D' F'
        (Huf : Uf.Wf (D c) -> Uf.Wf D')
        (Hcoinc : Uf.Wf (D c) -> coincides (D c) (I c) -> 
          eqns_of (I c) |- a = b -> coincides D' (I c))
        (Hcoinc' : Uf.Wf (D c) -> coincides (D c) (I c) -> 
          coincides D' ((Equation a b)::(I c)))
        (Hjust : Uf.Wf (D c) -> justify (D c) (F c) -> justify D' F')
        (Hcoh : Uf.Wf (D c) -> Diff.Wf (N c) -> 
          coherent (D c) (N c) -> coherent D' (N c))
        (Hmerge_congr : D' a === D' b)
        (Hmerge_uf : forall x y, D c x === D c y -> D' x === D' y)
        (Hmerge_range : Uf.range (D c) [<=] Uf.range D')
        (Hmerge_ext : forall p, List.In p (F c) -> List.In p F'),
        merge_spec a b c (Normal (mk_env G' D' (N c) F' (I c))).

    Lemma lcongr_merge : forall `{@Uf.Wf _ d} p P lu lv,
      lcongr d lu lv = true -> lcongr (fst (Uf.merge' d p P)) lu lv = true.
    Proof.
      intros d dwf p P; induction lu; destruct lv; simpl; auto.
      assert (Ha := Uf.merge'_find d p P a).
      assert (Ht := Uf.merge'_find d p P t0).
      destruct (eq_dec (fst (Uf.merge' d p P) a) (fst (Uf.merge' d p P) t0));
        destruct (eq_dec (d a) (d t0)); simpl; try (intro; discriminate).
      apply IHlu.
      rewrite H0 in Ha; contradiction H; order.
    Qed.
    Lemma justify_merge : forall `{@Uf.Wf _ d} p P F,
      justify d F -> justify (fst (Uf.merge' d p P)) F.
    Proof.
      intros; induction H0; simpl in *; constructor.
      apply lcongr_merge; assumption.
      assumption.
    Qed.
    Lemma coincides_merge : forall `{@Uf.Wf _ d} a b p P I,
      eqns_of I |- a = b -> solve (d a) (d b) = Subst p P ->
      coincides d I -> coincides (fst (Uf.merge' d p P)) I.
    Proof.
      intros; destruct H2 as [eqns]; exists ((a,b)::eqns).
      intros; right; auto.
      intros M HM; constructor; auto.
      intro z; simpl.
      assert (Ha := symmetry (H4 a)). assert (Hb := symmetry (H4 b)).
      assert (Hz := symmetry (H4 z)).

      unfold iter in *; simpl.
      destruct (Theory.iter eqns) as [f|]_eqn:Hf. 2:inversion_clear Ha.
      inversion_clear Ha; inversion_clear Hb; inversion_clear Hz; subst.
      assert (Hs := solve_m H5 H6); rewrite H1 in Hs.
      inversion Hs; subst; constructor.
      rewrite Uf.merge'_find.
      rewrite H11, H12, H7; reflexivity.
    Qed.
    Lemma coincides'_merge : forall `{@Uf.Wf _ d} a b p P I,
      solve (d a) (d b) = Subst p P ->
      coincides d I -> coincides (fst (Uf.merge' d p P)) ((Equation a b)::I).
    Proof.
      intros; destruct H1 as [eqns]; exists ((a,b)::eqns).
      intro; simpl; intuition.
      intros M HM; constructor; inversion HM; auto.
      intro z; simpl.
      assert (Ha := symmetry (H3 a)). assert (Hb := symmetry (H3 b)).
      assert (Hz := symmetry (H3 z)).

      unfold iter in *; simpl.
      destruct (Theory.iter eqns) as [f|]_eqn:Hf. 2:inversion_clear Ha.
      inversion_clear Ha; inversion_clear Hb; inversion_clear Hz; subst.
      assert (Hs := solve_m H4 H5); rewrite H0 in Hs.
      inversion Hs; subst; constructor.
      rewrite Uf.merge'_find; simpl.
      rewrite H6, H10, H11; reflexivity.
    Qed.
    Lemma coincides_weaken : 
      forall D I a b, coincides D I -> D a === D b -> 
        coincides D (Equation a b :: I).
    Proof.
      intros D0 I0 a b [eqns Hin Heqns Hiter] Heq; exists ((a, b)::eqns).
      intro; simpl; intuition.
      intros M HM; inversion HM; constructor (auto).
      intro z; simpl.
      assert (Ha := symmetry (Hiter a)). assert (Hb := symmetry (Hiter b)).
      assert (Hz := symmetry (Hiter z)).
      unfold iter in *; simpl.
      destruct (Theory.iter eqns) as [f|]_eqn:Hf. 2:inversion_clear Ha.
      inversion_clear Ha; inversion_clear Hb; inversion_clear Hz; subst.
      assert (R := transitivity (transitivity H Heq) (symmetry H0)).
      rewrite ((proj1 (solve_trivial _ _)) R).
      constructor (auto).
    Qed.
(*     Lemma coincides_weaken' :  *)
(*       forall D I a b, coincides D I -> equivX (D a) (D b) ->  *)
(*         coincides D (Equation a b :: I). *)
(*     Proof. *)
(*       intros D0 I0 a b [eqns Hin Heqns Hiter] Heq; exists ((a, b)::eqns). *)
(*       intro; simpl; intuition. *)
(*       intros M HM; inversion HM; constructor (auto). *)
(*       intro z; simpl. *)
(*       assert (Ha := symmetry (Hiter a)). assert (Hb := symmetry (Hiter b)). *)
(*       assert (Hz := symmetry (Hiter z)). *)
(*       unfold iter in *; simpl. *)
(*       destruct (Theory.iter eqns) as [f|]_eqn:Hf. 2:inversion_clear Ha. *)
(*       inversion_clear Ha; inversion_clear Hb; inversion_clear Hz; subst. *)
(* (*       destruct (iter eqns (make a)) as [ra|]; inversion_clear Ha; subst. *) *)
(* (*       destruct (iter eqns (make b)) as [rb|]; inversion_clear Hb; subst. *) *)
(* (*       destruct (iter eqns (make z)) as [rz|]; inversion_clear Hz; subst. *) *)
(*       rewrite solve_trivial'. *)
(*       constructor (auto). *)
(*       rewrite H, H0; auto. *)
(*     Qed. *)
    Lemma Ncoincides_weaken : 
      forall N I a b, Ncoincides N I -> Ncoincides N (Equation a b :: I).
    Proof.
      intros N0 I0 a b HNc; repeat intro.
      rewrite (HNc a0 b0); simpl; intuition congruence.
    Qed.

    Theorem merge_dec : forall a b e, merge_spec a b e (merge a b e).
    Proof.
      intros a b e; destruct e; simpl.
      destruct (N0 a b) as [ ]_eqn:HNab.
      (* - Inconsistence between N and D *)
      constructor.
      intros wf M Hsub; destruct wf; simpl_mk_env.
      intro abs; 
        contradiction (Ncoincides_submodel Ncorrect0 Hsub HNab abs).
      destruct (eq_dec (D0 a) (D0 b)).
      (* - Equation already true *)
      constructor; auto using coincides_weaken.
      reflexivity.
      (* - Real merge *)
      assert (cmerge := fun wf p P => @coincides_merge D0 wf a b p P I0).
      assert (c'merge := fun wf p P => @coincides'_merge D0 wf a b p P I0).
      destruct (solve_dec (D0 a) (D0 b)).
      (* -- Solved *)
      constructor; simpl; auto.
      intros; apply coincides_weaken; auto.
      reflexivity.
      (* -- Unsolvable *)
      constructor; intros wf M Hsub; destruct wf; simpl_mk_env.
      destruct Dcorrect0 as [eqns HinI Heqns Hiter]; intro abs.
      assert (Heqns' : models_list M ((a,b)::eqns)).
      constructor. exact abs. exact (Heqns M (submodel_eq_models_list Hsub)).

      intros x y; refine (implyX_entails _ Heqns').
      apply Hunsolv.
      transitivity (make a).
      apply implyX_weaken; symmetry;
        apply iter_correct; rewrite Hiter; reflexivity.
      transitivity (make b).
      apply implyX_Ax; intuition.
      apply implyX_weaken; apply iter_correct; rewrite Hiter; reflexivity.
      (* -- Subst *)
      assert (cmerge' := fun wf => cmerge wf p P); clear cmerge.
      assert (c'merge' := fun wf => c'merge wf p P); clear c'merge.
      assert (Hmerge := fun wf => @Uf.Wf_merge' _ _ D0 wf p P).
      assert (Hmrange := Uf.range_merge' D0 p P).
      assert (cohmerge := fun wf => @coherent_merge D0 wf p P N0).
      destruct (Uf.merge' D0 p P) as [D' touch]_eqn:HpP.
      destruct (incoherent D' N0 touch) as [ ]_eqn:Hincoh.
      (* -- Inconsistence between N and D' *)
      constructor; intros wf M Hsub; destruct wf; simpl_mk_env.
      destruct (incoherent_true Hincoh) as [x [y [Hx1 Hx2]]].
      intro abs; simpl fst in *.
      contradiction (Ncoincides_submodel Ncorrect0 Hsub Hx1).
(*       refine (Ncoincides_submodel Ncorrect0 Hsub Hx1 _). *)
      apply models_eq_sym; refine (coincides_submodel _ _ Hx2).
      apply (c'merge' Dwf0 (refl_equal _) Dcorrect0).
      constructor; auto.
      (* -- General case *)
      constructor (auto); simpl in *.
      (* --- justify *)
      intros wf HJ; assert (HJ' := justify_merge p P HJ).
      rewrite HpP in HJ'; exact (find_congr_equations_correct _ _ _ HJ').
      (* --- congr *)
      rewrite <- !Uf.merge'_find, HpP in Hsubst.
      rewrite Hsubst; reflexivity.
      (* --- extend uf *)
      intros; replace D' with (fst (Uf.merge' D0 p P)) by (rewrite HpP; auto).
      rewrite !Uf.merge'_find, H0; reflexivity.
      (* --- range *)
      rewrite Hmrange; reflexivity.
      (* --- extend *)
      intros; apply find_congr_equations_extend; auto.
    Qed.
    Corollary Wf_merge :
      forall `{Wf e} e' a b, eqns_of (I e) |- a = b -> 
        merge a b e = Normal e' -> Wf e'.
    Proof.
      intros; destruct H.
      destruct (merge_dec a b e); inversion H1; subst; clear H1; 
        constructor; simpl in *; auto.
    Qed.
    Corollary Wf_merge' :
      forall `{Wf e} e' a b, merge a b e = Normal e' -> 
        Wf (mk_env (G e') (D e') (N e') (F e') ((Equation a b)::(I e'))).
    Proof.
      intros; destruct H.
      destruct (merge_dec a b e); inversion H0; subst; clear H0; 
        constructor; simpl in *; auto using Ncoincides_weaken.
    Qed.

    Tactic Notation "decide" "merge" :=
      match goal with
        | |- context f [merge ?A ?B ?E] =>
          let wf := fresh "Hwfmerge" in
          let wf' := fresh "Hwfmerge'" in
            ((assert (wf := fun e' => @Wf_merge E _ e' A B);
              assert (wf' := fun e' => @Wf_merge' E _ e' A B))
            ||
              (assert (wf := fun w e' => @Wf_merge E w e' A B);
                assert (wf' := fun w e' => @Wf_merge' E w e' A B)
              ));
            destruct (merge_dec A B E); [|simpl_mk_env]
        | _ => fail 2 "No occurrence of merge found in the goal."
      end.
    Tactic Notation "decide" "merge" "in" hyp(H) :=
      match goal with
        | H : context f [merge ?A ?B ?E] |- _ =>
          let wf := fresh "Hwfmerge" in
          let wf' := fresh "Hwfmerge'" in
            ((assert (wf := fun e' => @Wf_merge E _ e' A B);
              assert (wf' := fun e' => @Wf_merge' E _ e' A B))
            ||
              (assert (wf := fun w e' => @Wf_merge E w e' A B);
                assert (wf' := fun w e' => @Wf_merge' E w e' A B)
              ));
(*             (assert (wf := fun e' => @Wf_merge E _ e' A B) || *)
(*               assert (wf := fun w e' => @Wf_merge E w e' A B)); *)
            destruct (merge_dec A B E); [|simpl_mk_env]; try discriminate H
        | _ => fail 2 "No occurrence of merge found in " H
      end.

    (** Specification of [clean_up]:
       - [clean_up c] returns [Normal c']
       -- [I c' = I c]
       -- [F c' = nil]
       -- [N c' = N c]
       -- [D c'] extends [D c]
       -- [Uf.range (D c) [<=] Uf.range D']
       -- all the equations in [F c] are true in [D c']
       -- [Wf] is preserved from [c] to [c']
       - [clean_up c] returns [Inconsistent]
       -- the conjunction of inputs [I c] is unsatisfiable
       *)
    Inductive clean_up_spec (e : t) : Exception t -> Prop :=
    | clean_up_Inconsistent :
      forall (Hclean_inc : Wf e -> forall M, submodel_eq M (I e) -> 
        forall x y, M |= x = y),
        clean_up_spec e Inconsistent
    | clean_up_Normal :
      forall G0 D0 
        (Hclean_wf : Wf e -> Wf (mk_env G0 D0 (N e) nil (I e)))
        (Hclean_uf : forall a b, D e a === D e b -> D0 a === D0 b)
        (Hclean_range : Uf.range (D e) [<=] Uf.range D0)
        (Hclean_congr : forall a b, List.In (a, b) (F e) -> D0 a === D0 b),
        clean_up_spec e (Normal (mk_env G0 D0 (N e) nil (I e))).
    Derive Inversion_clear clean_up_spec_inv with
      (forall e r, clean_up_spec e r) Sort Prop.
    Size clean_up_spec_inv.

    Theorem clean_up_dec : forall e, clean_up_spec e (clean_up e).
    Proof.
      intro e.
      apply clean_up_ind with (P := clean_up_spec); intros; subst.
      (* - No more pending equations *)
      constructor; simpl; intuition.
      (* - Merging another equation *)
      decide merge in e3; inversion e3; simpl in *; subst.
      inversion H; subst; clear H.
      (* -- The recursive call returned Inconsistent *)
      constructor; intros wf M; simpl_mk_env.
      apply Hclean_inc. destruct wf; constructor; simpl_mk_env; auto.
      apply Hcoinc; auto.
      intros M' HM'.
      assert (HJ := justify_coincides Dcorrect0 Fcorrect0 HM').
      inversion HJ; assumption.
      apply Hjust; auto; inversion Fcorrect0; assumption.
      (* -- The general case *)
      constructor; simpl in *.
      intro; apply Hclean_wf.
      destruct H; simpl in *.
      constructor; simpl; auto.
      apply Hcoinc; auto.
      intros M HM.
      assert (HJ := justify_coincides Dcorrect0 Fcorrect0 HM).
      inversion HJ; assumption.
      apply Hjust; auto; inversion Fcorrect0; assumption.
      auto.
      exact (transitivity Hmerge_range Hclean_range).
      intros a b [Hab|IH]; auto.
      inversion Hab; subst; auto.
      (* -- The merge returned Inconsistent *)
      constructor; intros wf M HM; destruct wf; simpl_mk_env.
      decide merge in e3; inversion e3; simpl in *; subst.
      inversion Fcorrect0; subst.
      (* refine (Hmerge_inc _ M HM _). *) (* TODO: DIVERGE! *)
      apply Hmerge_inc; try apply HM. (* TEMPORARY FIX... *)
      constructor; auto.
      assert (Hjc := justify_coincides Dcorrect0 Fcorrect0
        (submodel_eq_models_list HM)); inversion Hjc; subst.
      assumption.
    Qed.
    Definition pack (A : Type) (a : A) := a.
    Ltac fold_goal :=
      match goal with
        | |- ?G => change (pack G)
      end.
    Ltac unfold_goal :=
      match goal with
        | |- pack ?G => unfold pack
      end.
    Ltac my_inversion t c :=
      fold_goal;
      let Z := fresh "Z" in
        let R := fresh "R" in
          assert (Z := t);
            set (R := c) in *; clearbody R;
              inversion Z using clean_up_spec_inv; intros;
                subst; clear R Z; unfold_goal.
    Tactic Notation "decide" "clean_up" :=
      match goal with
        | |- context f [clean_up ?E] =>
          destruct (clean_up_dec E); [|simpl_mk_env]
(*           my_inversion (clean_up_dec E) (clean_up E); [|simpl_mk_env] *)
        | _ => fail 2 "No occurrence of clean_up found in the goal."
      end.
    Tactic Notation "decide" "clean_up" "in" hyp(H) :=
      match goal with
        | H : context f [clean_up ?E] |- _ =>
          destruct (clean_up_dec E); [|simpl_mk_env]; try discriminate H
(*           revert H; my_inversion (clean_up_dec E) (clean_up E); *)
(*           intro H; [|simpl_mk_env]; try discriminate H *)
        | _ => fail 2 "No occurrence of clean_up found in " H
      end.
    
    Corollary Wf_clean_up :
      forall `{Wf e} e', clean_up e = Normal e' -> Wf e'.
    Proof.
      intros.
      decide clean_up in H0; inversion H0; subst; auto.
    Time Qed. (* 0.67s *) (* 0.6s *) (* 0.32s *) (* 0.30 *)
    Size Wf_clean_up. (* 1121 *) (* 1007 *) (* 439 *) (* 436 *)

    (** Specification of [diff]:
       - [diff a b c] returns [Normal c']
       -- only [N] changes from [c] to [c']
       -- [a] and [b] are not congruent in [D c]
       -- provided [a] and [b] are added to the Uf, [Wf] is
       preserved from [c] to [c']
       - [diff a b c] returns [Inconsistent]
       -- [a] and [b] are congruent in [D c]
       (could also be : forall M, submodel_eq (I c) -> M |= a = b)
       *)
    Inductive diff_spec (a b : term) (c : t) : Exception t -> Prop :=
    | diff_spec_Inconsistent :
      forall (Hdiff_Inc : D c a === D c b),
        diff_spec a b c Inconsistent
    | diff_spec_Normal :
        forall 
          (Hdiff_neq : D c a =/= D c b)
          (Hdiff_wf : Wf c -> 
            a \In Uf.range (D c) -> b \In Uf.range (D c) ->
            Wf (mk_env (G c) (D c) 
              (Diff.separate (N c) a b) (F c) ((Disequation a b)::(I c)))),
        diff_spec a b c 
        (Normal (mk_env (G c) (D c) (Diff.separate (N c) a b) (F c) (I c))).
    (* NB : if we write [let N' := Diff.separate... in ...] instead
       of duplicating as we did, it doesnt work with [destruct diff_dec]
       later and we need inversion... *)

    Lemma Ncoincides_separate : 
      forall N I a b, Ncoincides N I -> 
        Ncoincides (Diff.separate N a b) ((Disequation a b)::I).
    Proof.
      intros  N0 I0 a b Ncorrect0 x y.
      assert (HN := Ncorrect0 x y); clear Ncorrect0.
      destruct (eq_dec y a).
      rewrite H in *; clear H.
      rewrite Diff.neqs_separate_1, add_iff; simpl.
      split; intros [H1|H2]; try tauto.
      change (b = x) in H1; subst; tauto.
      destruct H1. inversion H; left; reflexivity. tauto.
      destruct H2. inversion H; left; reflexivity. tauto.
      destruct (eq_dec y b).
      rewrite H0 in *; clear H0.
      rewrite Diff.neqs_separate_2, add_iff; simpl.
      split; intros [H1|H2]; try tauto.
      change (a = x) in H1; subst; tauto.
      destruct H1. inversion H0; left; reflexivity. tauto.
      destruct H2. inversion H0; left; reflexivity. tauto.
      rewrite Diff.neqs_separate_3; try (intro; auto).
      simpl; intuition congruence.
    Qed.
    Lemma coherent_diff : 
      forall D N a b, coherent D N -> D a =/= D b ->
        a \In Uf.range D -> b \In Uf.range D ->
        coherent D (Diff.separate N a b).
    Proof.
      intros D0 N0 a b Hcoh Hneq Ha Hb x y Hxy.
      rewrite <- Diff.neqs_iff in Hxy.
      destruct (eq_dec y a). change (y = a) in H; subst.
      split; auto; intro abs.
      rewrite Diff.neqs_separate_1, add_iff in Hxy; destruct Hxy.
      rewrite H in *; auto.
      refine ((proj2 (Hcoh x a _)) abs). 
      rewrite <- Diff.neqs_iff; assumption.
      destruct (eq_dec y b); try (rewrite H2 in *; clear H2).
      change (y = b) in H0; rewrite H0 in *; split; auto; intro abs.
      rewrite Diff.neqs_separate_2, add_iff in Hxy; destruct Hxy.
      rewrite H1 in *; auto.
      refine ((proj2 (Hcoh x b _)) abs). 
      rewrite <- Diff.neqs_iff; assumption.
      rewrite Diff.neqs_separate_3 in Hxy by (intro; auto).
      apply (Hcoh x y). rewrite <- Diff.neqs_iff; assumption.
    Qed.

    Theorem diff_dec : forall a b e, diff_spec a b e (diff a b e).
    Proof.
      intros a b e; destruct e; unfold diff; simpl.
      destruct (eq_dec (D0 a) (D0 b)); constructor.
      assumption.
      assumption.
      simpl; intro Z; inversion Z; constructor; auto; simpl_mk_env.
      apply Diff.Wf_separate.
      destruct Dcorrect0 as [eqns]; exists eqns; auto.
      apply Ncoincides_separate; assumption.
      apply coherent_diff; auto.
    Qed.
    Tactic Notation "decide" "diff" :=
      match goal with
        | |- context f [diff ?A ?B ?E] =>
          destruct (diff_dec A B E); [|simpl_mk_env]
        | _ => fail 2 "No occurrence of diff found in the goal."
      end.
    Tactic Notation "decide" "diff" "in" hyp(H) :=
      match goal with
        | H : context f [diff ?A ?B ?E] |- _ =>
          destruct (diff_dec A B E); [|simpl_mk_env]; try discriminate H
        | _ => fail 2 "No occurrence of diff found in " H
      end.

    Theorem Wf_diff : forall `{Wf e} e' a b, 
      a \In Uf.range (D e) -> b \In Uf.range (D e) ->
      diff a b e = Normal e' -> 
      Wf (mk_env (G e') (D e') (N e') (F e') ((Disequation a b)::(I e'))).
    Proof.
      intros; decide diff in H2; inversion H2; 
        destruct H; constructor (auto).
      apply Diff.Wf_separate.
      destruct Dcorrect0 as [eqns]; exists eqns; auto.
      apply Ncoincides_separate; assumption.
      simpl in *; apply coherent_diff; auto.
    Qed.

    (** About [assume] *)
    Definition input_assume (D : Uf.t) (N : Diff.t (term:=term)) (i : input) :=
      match i with
        | Equation a b => D a === D b
        | Disequation a b => N a b = true
      end.
    Definition input_range (D D' : Uf.t) (i : input) :=
      match i with
        | Equation a b | Disequation a b =>
          {b; {a; Uf.range D}} [<=] Uf.range D'
      end.
    Inductive assume_spec (i : input) (e : t) : Exception t -> Prop :=
    | assume_spec_Input :
      forall G' (D' : Uf.t) (N' : Diff.t)
        (Hassume_uf : forall a b, D e a === D e b -> D' a === D' b)
        (Hassume_N : forall a b, N e a b = true -> N' a b = true)
        (Hassume_wf : Wf e -> Wf (mk_env G' D' N' nil (i::(I e))))
        (Hassume_input : input_assume D' N' i)
        (Hassume_range : input_range (D e) D' i),
        assume_spec i e (Normal (mk_env G' D' N' nil (i::(I e))))
    | assume_spec_Inconsistent :
      forall (Hassume_inc : Wf e ->
        forall M, submodel_eq M (I e) -> M (input_to_lit i) ->
          forall x y, M |= x = y),
      assume_spec i e Inconsistent.

    Theorem assume_dec : forall i e, assume_spec i e (assume i e).
    Proof.
      intros i e; unfold assume.
      destruct e; destruct i as [a b | a b]; simpl.
      (* - equation [a = b] *)
      do 2 decide add_term.
      decide merge.
      (* -- the merge returned Inconsistent *)
      constructor; intros wf M HM Hab; simpl in *.
      apply Hmerge_inc; auto.
(*       change (M |= a <> b); apply Hmerge_inc; auto. *)
      decide clean_up.
      (* -- the clean-up returned Inconsistent *)
      constructor; intros wf M HM; simpl in *.
      intro abs; generalize (submodel_cons_eq abs HM).
      apply Hclean_inc; auto.
      refine (Hwfmerge'  _ _ (refl_equal _)); auto.
      (* -- the general case *)
      constructor; simpl_mk_env.
      auto. auto.
      intro Z; apply Hclean_wf.
      refine (Hwfmerge' _ _ (refl_equal _)); auto.
      apply Hclean_uf; assumption.
      refine (transitivity _ Hclean_range).
      refine (transitivity _ Hmerge_range).
      refine (transitivity _ Hadd_range).
      apply add_s_m; auto.
      (* - disequation [a <> b] *)
      do 2 decide add_term.
      decide clean_up.
      (* -- the clean-up returned Inconsistent *)
      constructor; intros wf M HM Hab; simpl in *.
      apply Hclean_inc; auto.
(*       intros _; revert HM; apply Hclean_inc; auto. *)
      decide diff; simpl_mk_env.
      (* -- the diff returned Inconsistent *)
      constructor; intros wf M HM Hab; simpl in *.
      contradiction Hab; refine (coincides_submodel _ HM Hdiff_Inc).
(*       intro abs; apply abs. *)
(*       refine (coincides_submodel _ HM Hdiff_Inc). *)
      destruct Hclean_wf; auto.
      (* -- the general case *)
      assert (cut : {b; {a; Uf.range D0}} [<=] Uf.range D1).
      refine (transitivity _ Hclean_range).
      refine (transitivity _ Hadd_range).
      apply add_s_m; auto.
      constructor; auto.
      apply Diff.separate_conservative.
      intro; apply Hdiff_wf; auto.
      apply cut; apply add_2; apply add_1; reflexivity.
      apply cut; apply add_1; reflexivity.
      apply Diff.are_diff_separate_1.
    Time Qed. (* 1.41s *) (* ... *) (* 0.66s *) (* 0.77s *)
    Size assume_dec. (* 5719 *) (* ... *) (* 3538 *) (* 3532 *)
    Tactic Notation "decide" "assume" :=
      match goal with
        | |- context f [assume ?A ?E] =>
          destruct (assume_dec A E); [simpl_mk_env|]
        | _ => fail 2 "No occurrence of diff found in the goal."
      end.
    Tactic Notation "decide" "assume" "in" hyp(H) :=
      match goal with
        | H : context f [assume ?A ?E] |- _ =>
          destruct (assume_dec A E); [simpl_mk_env|]; try discriminate H
        | _ => fail 2 "No occurrence of assume found in " H
      end.
    Corollary Wf_assume : 
      forall `{Wf e} i e', assume i e = Normal e' -> Wf e'.
    Proof.
      intros e wf i e' H; decide assume in H; 
        inversion H; subst; auto.
    Qed.
    
    (** About [are_equal] *)
    Inductive are_equal_spec (a b : term) (e : t) : bool -> Prop :=
    | are_equal_spec_true : 
      forall (Hare_equal : Wf e -> 
        forall M, submodel_eq M (I e) -> M |= a = b),
        are_equal_spec a b e true
    | are_equal_spec_false : 
      forall (Hare_equal_input : Wf e -> ~List.In (Equation a b) (I e)),
        are_equal_spec a b e false.
    
    Theorem are_equal_dec : forall a b e, 
      are_equal_spec a b e (are_equal a b e).
    Proof.
      intros; destruct e; unfold are_equal.
      do 2 decide add_term.
      decide clean_up.
      (* - true because Inconsistent *)
      constructor; intros wf M Hsub; auto.
(*       contradiction Hclean_inc with M; auto. *)
      destruct (eq_dec (D1 a) (D1 b)); constructor.
      (* - general true *)
      intro wf; destruct Hclean_wf; auto; simpl_mk_env.
      intros M HM; apply coincides_submodel with D1 I0; assumption.
      (* - general false *)
      intro wf; destruct Hclean_wf; auto; simpl_mk_env.
      intro Hin; apply H.
      apply coincides_inputs with I0; auto.
    Time Qed. (* 0.58 *) (* 0.28 *) (* 0.28 *)
    Size are_equal_dec. (* 2464 *) (* 1449 *) (* 1446 *)

    (** About [are_diff] *)
    Inductive are_diff_spec (a b : term) (e : t) : bool -> Prop :=
    | are_diff_spec_true : 
      forall (Hare_diff : Wf e -> 
        forall M, submodel_eq M (I e) -> M |= a <> b),
        are_diff_spec a b e true
    | are_diff_spec_false : 
      forall (Hare_diff_input : Wf e -> ~List.In (Disequation a b) (I e)),
        are_diff_spec a b e false.

    (* ACHTUNG : here I use the fact that I  know two terms that are for
       sure different in any model I consider. This I can do only if there
       are interpreted terms. With the empty theory, for instance, there exists
       a model where every equation is true, but this is fine since the emtpy
       theory never returns Unsolvable. 
       So it should be up to a theory raising Unsolvable (and thus
       Inconsistent) to justify that it is indeed impossible that
       such an equation is true in practice. I should change back the
       inconsistent specs from 'everything is true' to 'the unsolvable
       equation is false' in CCX, and let the theory  make the link between
       the two using implyX_entails and two pure different terms for instance.
       However this is cumbersome for many technical reasons and since I also
       use models with interpreted arithmetic even for the empty theory, there
       always exist distinct terms in my models and therefore I can prove the
       following lemma here and prove that [are_diff] is correct.
       *)
    Lemma no_trivial_model : forall M, ~(forall x y, M |= x = y).
    Proof.
      intros M H; assert (abs := 
        H (app (Cst DomainNat 0) nil) (app (Cst DomainNat 1) nil)).
      rewrite models_eq_iff in abs by reflexivity.
      assert (H1 : has_type (Ergo.varmaps_vty M) (Ergo.varmaps_vsy M)
        (app (Cst DomainNat 0) tnil) (typeArith DomainNat) = true) 
      by reflexivity.
      assert (H2 : has_type (Ergo.varmaps_vty M) (Ergo.varmaps_vsy M)
        (app (Cst DomainNat 1) tnil) (typeArith DomainNat) = true) 
      by reflexivity.
      rewrite <- (Term.replace' _ _ _ _ _ H1 H2) in abs.
      vm_compute in abs; discriminate abs.
    Qed.
    Theorem are_diff_dec : forall a b e, 
      are_diff_spec a b e (are_diff a b e).
    Proof.
      intros; destruct e; unfold are_diff.
      decide assume; constructor.
      (* - equation did not raise Inconsistent *)
      simpl; intro wf; destruct Hassume_wf; auto.
      intro Hin; simpl_mk_env.
      refine ((proj2 (coherence0 a b _)) _).
      rewrite <- Diff.neqs_iff, (Ncorrect0 a b); left; right; assumption.
      apply Hassume_input.
      (* - equation did raise Inconsistent *)
      intros; intro abs; refine (@no_trivial_model M _).
      exact (Hassume_inc H M H0 abs).
    Qed.
    
    (** About [query] *)
    Inductive query_spec (q : input) (e : t) : bool -> Prop :=
    | query_spec_true : 
      forall (Hquery : Wf e -> 
        forall M, submodel_eq M (I e) -> M (input_to_lit q)),
      query_spec q e true
    | query_spec_false : 
      forall (Hquery : Wf e -> ~ List.In q (I e)),
        query_spec q e false.

    Theorem query_dec : forall q e, query_spec q e (query q e).
    Proof.
      intros; unfold query; destruct e; destruct q.
      destruct (are_equal_dec a b (mk_env G0 D0 N0 F0 I0)); constructor.
      exact Hare_equal.
      exact Hare_equal_input.
      destruct (are_diff_dec a b (mk_env G0 D0 N0 F0 I0)); constructor.
      exact Hare_diff.
      exact Hare_diff_input.
    Qed.

    (** Final toplevel properties on [assume], [query], etc 
       for the module signature. *)
    Property assumed_assume :
      forall c i c', assume i c = Normal c' -> assumed c' = i::(assumed c).
    Proof.
      intros; destruct c;
        decide assume in H; inversion H; subst; reflexivity.
    Qed.

    Theorem query_assumed : forall  `{Wf c} i,
      List.In i (assumed c) -> query i c = true.
    Proof.
      intros; destruct (query_dec i c).
      reflexivity.
      contradiction (Hquery H H0).
    Qed.

    Theorem assumed_inconsistent :
      forall `{Wf c} i, assume i c = Inconsistent ->
        query (match i with
                 | Equation a b => Disequation a b
                 | Disequation a b => Equation a b
               end) c = true.
    Proof.
      intros; unfold query; destruct i.
      unfold are_diff.
      destruct (assume (Equation a b) c); [discriminate | reflexivity].
      unfold are_equal.
      unfold assume in H0.
      do 2 decide add_term.
      decide clean_up.
      reflexivity.
      decide diff in H0; simpl_mk_env.
      destruct (eq_dec (D0 a) (D0 b)); auto.
    Qed.

    Theorem query_true : forall `{Wf c} i, query i c = true ->
      forall M, submodel_eq M (assumed c) -> M (input_to_lit i).
    Proof.
      intros.
      destruct (query_dec i c); auto.
      discriminate.
    Qed.
  End Specs.
End RAWCCX.

Module RAWCCE := RAWCCX EmptyTheory.
Require Import TheoryArith.
Module RAWCCA := RAWCCX ArithTheory.

Module TestsDeCCXE.
  Import RAWCCE. Import Quote.
  Definition e : t := empty.

  (* symbols *)
  Local Notation a := (Unint End_idx End_idx).
  Local Notation b := (Unint End_idx (Left_idx End_idx)).
  Local Notation c := (Unint End_idx (Right_idx End_idx)).
  Local Notation f := (Unint End_idx (Left_idx (Left_idx End_idx))).
  Local Notation g := (Unint End_idx (Left_idx (Right_idx End_idx))).

  (* terms *)
  Local Notation ta := (app a nil).
  Local Notation tb := (app b nil).
  Local Notation tc := (app c nil).
  Local Notation fa := (app f (ta::nil)).
  Local Notation fb := (app f (tb::nil)).
  Local Notation fc := (app f (tc::nil)).
  Local Notation f2a := (app f (fa::nil)).
  Local Notation f3a := (app f (f2a::nil)).
  Local Notation f4a := (app f (f3a::nil)).
  Local Notation f5a := (app f (f4a::nil)).
  Local Notation ga := (app g (ta::nil)).
  Local Notation gb := (app g (tb::nil)).
  Local Notation gc := (app g (tc::nil)).

  (* printing the state *)
  Definition strip (c : t) :=
    let 'mk_env G D N F I := c in
    let Gs := 
      MapInterface.fold (fun k v acc => (k, elements v)::acc) G nil in
    let Ds := 
      MapInterface.elements (Uf.this D) in
    let Ns := 
      MapInterface.fold (fun k v acc => (k, elements v)::acc) N nil in
        (Gs, Ds, Ns, F, I).
  Ltac print e :=
    let z := eval vm_compute in (strip e) in
    match constr:z with
      | (?G,?D,?N,?F,?I) =>
        idtac "Use : " G;
        idtac "UF : " D;
        idtac "Neqs : " N;
        idtac "Pending : " F;
        idtac "Assumed :" I
      | _ => idtac "Inconsistent"
    end.
  Goal True. print e. Abort.

  (* dealing with failures *)
  Parameter error : t.
  Local Notation "'do' x" := (match x with Normal e => e | Inconsistent => error end)
    (at level 30).

  Module TestNewUse.
    Definition e1 := do (assume (Disequation fa fc) e).
    Goal True. print e1. Abort.
    Eval vm_compute in query (Equation fa fc) e1.
    Definition e2 := do (assume (Equation tc tb) e1).
    Goal True. print e2. Abort.
    Definition e3 := do (assume (Equation tb ta) e2).
    Goal True. print e3. Abort.
    Eval vm_compute in query (Disequation ta tb) e2.
    Eval vm_compute in query (Disequation tb ta) e2.
  End TestNewUse.
  
  Eval vm_compute in query (Equation ta tc) e. (* false *)
  Eval vm_compute in query (Equation f3a f3a) e. (* true *)
  Eval vm_compute in query (Disequation ta tb) e. (* false *)
  Eval vm_compute in query (Disequation ta ta) e. (* false *)
  
  Definition e1 := do (assume (Equation ta tb) e).
  Goal True. print e1. Abort. (* ta et tb mergés *)
  Eval vm_compute in query (Equation ta fa) e1. (* false *)
  Eval vm_compute in query (Equation ta tb) e1. (* true *)
  Eval vm_compute in query (Equation tb ta) e1. (* true *)
  Eval vm_compute in query (Disequation tb ta) e1. (* false *)
  Eval vm_compute in query (Equation fb fc) e1. (* false *)
  Eval vm_compute in query (Equation fb fa) e1. (* true *)

  Definition e1' := add_term fa e1.
  Goal True. print e1'. Abort.  (* Use bien mis à jour *)
  Definition e1'' := add_term fb e1'.
  Goal True. print e1''. Abort. (* fa et fb bien mergés *)

  Definition e2 := do (assume (Disequation fb fc) e1).
  Goal True. print e2. Abort. (* Use et Neqs bien mis à jour *)
  Eval vm_compute in query (Equation fb fc) e2. (* false *)
  Eval vm_compute in query (Disequation fc fb) e2. (* true *)
  Eval vm_compute in query (Equation fa fc) e2. (* false *)
  Eval vm_compute in query (Disequation fa fc) e2. (* true *)
  Eval vm_compute in query (Equation fa fb) e2. (* true *)
  Eval vm_compute in query (Equation tb tc) e2. (* false *)
  Eval vm_compute in query (Disequation tb tc) e2. (* true *)
  (* Tout semble OK. *)

  (* test de f3a = a -> f5a = a -> fa = a *)
  Definition e3 := do (assume (Equation f5a ta) 
    (do (assume (Equation f3a ta)) e)).
  Time Eval vm_compute in query (Equation fa ta) e3. (* true *)
  Goal True. print e3. Abort. (* tous pointent vers (et utilisent) f(f(a)) *)
End TestsDeCCXE.

Module TestsDeCCXA.
  Import RAWCCA. Import Quote.
  Definition e : t := empty.

  (* symbols *)
  Local Notation a := (Unint End_idx End_idx).
  Local Notation b := (Unint End_idx (Left_idx End_idx)).
  Local Notation c := (Unint End_idx (Right_idx End_idx)).
  Local Notation f := (Unint End_idx (Left_idx (Left_idx End_idx))).
  Local Notation g := (Unint End_idx (Left_idx (Right_idx End_idx))).
  Local Notation x := (Unint End_idx (Right_idx (Left_idx End_idx))).
  Local Notation one := (Cst DomainZ 1%Z).
  Local Notation zero := (Cst DomainZ 0%Z).

  (* terms *)
  Local Notation ta := (app a nil).
  Local Notation tb := (app b nil).
  Local Notation tc := (app c nil).
  Local Notation fa := (app f (ta::nil)).
  Local Notation fb := (app f (tb::nil)).
  Local Notation fc := (app f (tc::nil)).
  Local Notation f2a := (app f (fa::nil)).
  Local Notation f3a := (app f (f2a::nil)).
  Local Notation f4a := (app f (f3a::nil)).
  Local Notation f5a := (app f (f4a::nil)).
  Local Notation ga := (app g (ta::nil)).
  Local Notation gb := (app g (tb::nil)).
  Local Notation gc := (app g (tc::nil)).
  Local Notation tx := (app x nil).
  Local Notation tone := (app one nil).
  Local Notation tzero := (app zero nil).
  Local Notation txzero := (app (Op DomainZ Plus) (tzero::tx::nil)).
  Local Notation tf1 := (app f (tone::nil)).
  Local Notation tfx := (app f (tx::nil)).
  Local Notation tfxzero := (app f (txzero::nil)).

  Local Notation "'monome' t" := 
    (QArith_base.Qmake 0 1, (t, QArith_base.Qmake 1 1)::nil)(at level 0).
  Local Notation bottom := (QArith_base.Qmake 1 7).

  (* printing the state *)
  Definition stripR (r : R) := 
    let r := CPolynoms.FULL._this r in (fst r, MapInterface.elements (snd r)).
  Definition strip (c : t) :=
    let 'mk_env G D N F I := c in
    let Gs := 
      MapInterface.fold (fun k v acc => (stripR k, elements v)::acc) G nil in
    let Ds := 
      List.map (fun tk => (fst tk, stripR (snd tk)))
      (MapInterface.elements (Uf.this D)) in
    let Ns := 
      MapInterface.fold (fun k v acc => (k, elements v)::acc) N nil in
        (Gs, Ds, Ns, F, I).
  Ltac print e :=
    let z := eval vm_compute in (strip e) in
    match constr:z with
      | (?G,?D,?N,?F,?I) =>
        idtac "Use : " G;
        idtac "UF : " D;
        idtac "Neqs : " N;
        idtac "Pending : " F;
        idtac "Assumed : " I
      | _ => idtac "Inconsistent"
    end.
  Goal True. print e. Abort.

  (* dealing with failures *)
  Parameter error : t.
  Local Notation "'do' x" := (match x with Normal e => e | Inconsistent => error end)
    (at level 30).

  Module TestNewUse.
(*     Definition e1 := do (add fa e). *)
(*     Definition e1' := do (add_term tc e1). *)
    
(*     Set Printing All. *)
(*     Print R_OT. *)
(*     Eval vm_compute in compare (H:=R_OT) (make ta) (make tc). *)
(*     Definition G2 := MapInterface.add (make tc) {fc} (G e1'). *)
(*     Typeclasses eauto := debug. *)
(*     Eval vm_compute in (MapInterface.elements G2). *)

(*     Eval vm_compute in (elements (Use.find (G e1') (make fc))). *)
(*     Eval vm_compute in (lleaves (D e1') (tcons tc tnil)). *)
(*     Eval vm_compute in (MapInterface.elements (G e1')). *)
(*     Eval vm_compute in find_add_equations (G e1') (D e1') (F e1') fc  *)
(*       (lleaves (D e1') (tcons tc tnil)). *)
(*     Eval vm_compute in (Use.using_all (G e1') (lleaves (D e1') (tcons tc tnil))). *)
(*     Definition e1'' := do ( ). *)
(*     Goal True. print e1''. Abort. *)

    Definition e1 := do (assume (Disequation fa fc) e).    
    Goal True. print e1. Abort.
    Eval vm_compute in query (Equation fa fc) e1.
    Definition e2 := do (assume (Equation tc tb) e1).
    Goal True. print e2. Abort.
(*     Definition e3 := do (assume (Equation tb ta) e2). *)
    Eval vm_compute in query (Equation ta tb) e2.
    Eval vm_compute in query (Disequation tb ta) e2.
  End TestNewUse.
  
  Eval vm_compute in query (Equation ta tc) e. (* false *)
  Eval vm_compute in query (Equation f3a f3a) e. (* true *)
  Eval vm_compute in query (Disequation ta tb) e. (* false *)
  Eval vm_compute in query (Disequation ta ta) e. (* false *)
  
  Definition e1 := do (assume (Equation ta tb) e).
  Goal True. print e1. Abort. (* ta et tb mergés *)
  Eval vm_compute in query (Equation ta fa) e1. (* false *)
  Eval vm_compute in query (Equation ta tb) e1. (* true *)
  Eval vm_compute in query (Equation tb ta) e1. (* true *)
  Eval vm_compute in query (Disequation tb ta) e1. (* false *)
  Eval vm_compute in query (Equation fb fc) e1. (* false *)
  Eval vm_compute in query (Equation fb fa) e1. (* true *)

  Definition e1' := add_term fa e1.
  Goal True. print e1'. Abort.  (* Use bien mis à jour *)
  Definition e1'' := add_term fb e1'.
  Goal True. print e1''. Abort. (* fa et fb bien mergés *)

  Definition e2 := do (assume (Disequation fb fc) e1).
  Goal True. print e2. Abort. (* Use et Neqs bien mis à jour *)
  Eval vm_compute in query (Equation fb fc) e2. (* false *)
  Eval vm_compute in query (Disequation fc fb) e2. (* true *)
  Eval vm_compute in query (Equation fa fc) e2. (* false *)
  Eval vm_compute in query (Disequation fa fc) e2. (* true *)
  Eval vm_compute in query (Equation fa fb) e2. (* true *)
  Eval vm_compute in query (Equation tb tc) e2. (* false *)
  Eval vm_compute in query (Disequation tb tc) e2. (* true *)
  (* Tout semble OK. *)

  (* test de f3a = a -> f5a = a -> fa = a *)
  Definition e3 := do (assume (Equation f5a ta) 
    (do (assume (Equation f3a ta)) e)).
  Time Eval vm_compute in query (Equation fa ta) e3. (* true *)
  Goal True. print e3. Abort. (* tous pointent vers (et utilisent) f(f(a)) *)

  (* test incluant de l'arithmétique *)
  Definition ea1 := do (assume (Equation tone tx) e).
  Goal True. print ea1. Abort. (* t1 => [1], tx => [1] *)
  Definition ea2' := add_term tzero (add_term ta ea1).
  Goal True. print ea2'. Abort.
  Definition ea2'' := add_term txzero ea2'.
  Goal True. print ea2''. Abort.
  Definition ea2''' := add_term tfxzero ea2''.
  Goal True. print ea2'''. Abort.
  Definition ea2'''' := do (merge tfxzero ta ea2''').
  Goal True. print ea2''''. Abort.
  Definition ea2''''' := add_term tf1 ea2''''.
  Goal True. print ea2'''''. Abort.
    
  Definition ea2 := do (assume (Equation tfxzero ta) ea1).
  Goal True. print ea2. Abort.
  Eval vm_compute in (query (Equation tf1 ta) ea2). (* true *)
  Eval vm_compute in (query (Disequation tone tzero) e). (* true *)
End TestsDeCCXA.

Module CCX (Import T : THEORY) <: CCX_SIG.
  Module RAW := RAWCCX T.

  Inductive t_ := mk_t {
    this :> RAW.t;
    this_wf : RAW.Specs.Wf this
  }.
  Definition t := t_.

  Definition empty : t := mk_t RAW.Specs.Wf_empty.
  
  Definition assume (i : input) (e : t) : Exception t :=
    match RAW.assume i e as a 
      return RAW.assume i e = a -> Exception t with
      | Normal e' => fun H => Normal (@mk_t e' 
        (@RAW.Specs.Wf_assume _ (this_wf e) i e' H))
      | Inconsistent => fun _ => Inconsistent
    end (refl_equal _).

  Definition query (i : input) (e : t) :=
    RAW.query i e.

  Definition assumed (e : t) := RAW.assumed (this e).

  Module Specs.
    Lemma this_assume : forall c c' i, assume i c = Normal c' ->
      RAW.assume i (this c) = Normal (this c').
    Proof.
      intros; unfold assume in *; destruct c; destruct c'; simpl in *.
      set (Z := RAW.Specs.Wf_assume (i:=i)) in *; clearbody Z.
      destruct (RAW.assume i this0); simpl.
      inversion H; reflexivity.
      discriminate.
    Qed.
    Lemma this_assume_inc : forall c i, assume i c = Inconsistent ->
      RAW.assume i (this c) = Inconsistent.
    Proof.
      intros; unfold assume in *; destruct c; simpl in *.
      set (Z := RAW.Specs.Wf_assume (i:=i)) in *; clearbody Z.
      destruct (RAW.assume i this0); simpl.
      discriminate.
      reflexivity.
    Qed.

    Theorem assumed_empty : assumed empty = nil.
    Proof.
      reflexivity.
    Qed.
    Theorem assumed_assume :
      forall c i c', assume i c = Normal c' -> assumed c' = i::(assumed c).
    Proof.
      intros.
      assert (H' := this_assume H).
      unfold assumed.
      rewrite (@RAW.Specs.assumed_assume c i c'); auto.
    Qed.
    Theorem assumed_inconsistent : 
      forall c i, assume i c = Inconsistent -> 
        query (match i with 
                 | Equation a b => Disequation a b
                 | Disequation a b => Equation a b 
               end) c = true.
    Proof.
      intros c i H; destruct c as [c wfc].
      assert (H' := this_assume_inc H); simpl in *.
      unfold query.
      apply RAW.Specs.assumed_inconsistent; auto.
    Qed.
    Theorem query_true : forall c i, query i c = true ->
      forall M, submodel_eq M (assumed c) -> M (input_to_lit i).
    Proof.
      destruct c; unfold query, assumed; simpl.
      apply RAW.Specs.query_true.
    Qed.
    Theorem query_assumed : forall c i, 
      List.In i (assumed c) -> query i c = true.
    Proof.
      destruct c; unfold query, assumed; simpl.
      apply RAW.Specs.query_assumed.
    Qed.
  End Specs.
End CCX.
Module CCE := CCX EmptyTheory.
Module CCA := CCX ArithTheory.
