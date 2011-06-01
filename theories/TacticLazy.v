(** This file contains a functor building a reflexive tactic
   for a [CNF] module on lazy literals. *)
Require Import Quote Ergo Setoid.
Require Import Adequation Env Dpll LLazy SemLazy CNFLazyCommon List.

(** * The functor [Adequation]

   [Adequation] is a functor parameterized by a [CNFLZAY_INTERFACE] and
   that derives semantical properties about CNF formulas on lazy literals.
   More precisely, it is the bridge between our notion of semantics as
   defined in [Semantics.SEM_INTERFACE] and Coq's notion of truth.

   The main result of this functor is that given a formula [f],
   if [interp v f] is in Coq's context, then [f] is satisfiable
   from the semantical point of view. Its model is simply a canonical
   model where each literal interprets to the formula it represents.
*)
Module AdequationLazy (Import F : CNFLAZY_INTERFACE).
  Definition interp : varmaps -> formula -> Prop := F.interp.

  Section Adequation.
    Variable v : varmaps.
    
    (** The interpretation of the literals is a canonical model. *)
    Definition canonical_model : SEMLAZY.model := v.
   
    (** Adequation means that the canonical model is indeed a model
       of the formula we built, when it is in the context. *)
    Lemma adequation : 
      forall (f: F.formula), F.interp v f ->
        Sem.sat_goal canonical_model (F.make f).
    Proof with (eauto with typeclass_instances).
      intros; unfold F.interp in *; simpl in *.
      intros c Hc; exists f; split; auto.
      assert (Hc' := (proj1 ((F.make_1 f) c) Hc)).
      refine ((proj1 ((singleton_1 Hc') f)) _)...
      apply singleton_2; reflexivity.
    Qed.
  End Adequation.
End AdequationLazy.

(** * The functor [LoadTactic]

   This functor depends on a CNF on lazy literals and a DPLL procedure
   on this type of formulae. It builds a tactic that can then be 
   loaded and used interactively by users.
   *)
Module LoadTactic (Import F : CNFLAZY_INTERFACE) (Import LS : DPLL F).
  Module L := LLAZY.
  Module Import AD := AdequationLazy F.
  
  (** A wrapper around the dpll function to compute the counter model
     as well.

     Note: this is CRITICAL that the counter-model be returned in 
     a very simple/compact representation at the end of the proof search
     instead of just returning a [LSet.t]. Indeed, lazy literals can grow
     quite large (because of proofs) but their computational contents remain
     small and they can still be handled efficiently by the bytecode 
     interpreter. If however, a call to the bytecode interpreter returns
     with a [LSet.t] containing big objects, the time spent by the system
     to convert this object back from bytecode will be a total bottleneck.
     Therefore, we need to finish the work in a single call to [vm_compute]
     and clean up the counter model before returning to the caller.
     *)
  Inductive Res : Type :=
  | Sat : list (LITINDEX.atom * bool) -> Res
  | Unsat.
  Require Import String.
  Definition dpll (v : varmaps) F :=
    match dpll F with
      | LS.Unsat => Unsat
      | LS.Sat M =>
        Sat (fold (fun l acc => 
          match L.this l with 
            | L.RAW.Lit (Some atom, b) => (atom, b)::acc
              (** Before, we used to interpret literals and return Prop's
                 but we defer interpretation to the [print_model] tactic.
                 Less efficient but allows to only unfold the reification 
                 layer instead of computing everything *)
              (* let ia := *)
              (*   match atom with *)
              (*     | Some (LITINDEX.Atom _) => LITINDEX.interp_atom v atom *)
              (*     | Some (LITINDEX.Equation t1 t2) => *)
              (*       match binterp_eq v t1 t2 with *)
              (*         | Some p => p *)
              (*         | None => ("dummy" = "proposition")%string *)
              (*       end *)
              (*     | None => True *)
              (*   end *)
              (*   in (ia, b)::acc *)
            | _ => acc 
          end) (E.assumed M) nil)
    end.
  
  (** Corollary of the Adequation section & the soundness of DPLL: 
     if [dpll] returns [Unsat] on an abstract formula [F], then its 
     interpretation cannot be true.
     *)
  Corollary validity : 
    forall (F : formula) (v : varmaps), 
      dpll v F = Unsat -> ~(F.interp v F).
  Proof.
    intros F v Hunsat HF; unfold dpll in Hunsat.
    case_eq (LS.dpll F); intros; rewrite H in Hunsat.
    discriminate.
    assert (unsat := LS.dpll_correct _ H).
    refine ((LS.dpll_correct _ H) (canonical_model v) _ _); simpl.
    intros l Hl; contradiction (empty_1 Hl).
    exact (adequation v F HF).
  Qed.

  Definition dpll' v (F : fform) :=
    dpll v (F.Conversion.mk_form F).
  (** Validity lemma BEFORE I added the well typedness constraint on CNFs *)
(*   Corollary validity' : *)
(*     forall (F : fform) (v : varmaps), dpll' v F = Unsat -> ~(finterp v F). *)
(*   Proof. *)
(*     intros; intro N. *)
(*     apply (F.Conversion.cnf v F); intro R. *)
(*     rewrite R in N. *)
(*     exact (validity _ v H N). *)
(*   Qed. *)
  Corollary validity' :
    forall (f : fform) (F : Prop) (v : varmaps), 
      dpll' v f = Unsat -> binterp v f = Some F -> ~F.
  Proof.
    intros; intro N.
    apply (F.Conversion.cnf v f).
    rewrite well_typed_formula_iff_binterp; exists F; assumption.
    intro R; rewrite (binterp_is_finterp v f F H0) in N.
    rewrite R in N.
    exact (validity _ v H N).
  Qed.

  (** The 3 following routines are used to dsplay countermodel in a nice way.
     Propositional atoms are printed using [lookup] but the original reified 
     literal is not reduced (in contrast to what [vm_compute] would do.
     Similarly, [print_reified_eq] simplifies an equality between reified terms
     back to the equality between original terms, and displays it with [idtac].
     *)
  Require Import ZArith.
  Ltac print_reified_eq vt vs t u b :=
    let ieq := constr:(Term.eq vt vs t u) in
    let r := eval compute
      [
        Term.eq Term.int Term.type_of Term.has_type Term.have_type 
        Term.tinterp Term.interp' Term.interp Term.interps_
        Term.lookup Term.dom_interp
        Term.lookup_type Term.type_of Term.type_ind Term.type_rect
        Term.types_of Term.tequal Term.typeBinop Term.typeUnop
        projT1 projT2 varmap_find Term.mk_depvmap Term.interp_op
        Term.dom_equal Term.mk_symbol Term.symbol_equal Term.arithop_equal
        Zeq_bool Zcompare Pcompare eq_ind eq_ind_r eq_rect Term.tequal_1 
        index_eq index_ind index_rect sym_eq
      ] 
      in ieq in
      match constr:r with
        | Some (existT _ _ ?x) = Some (existT _ _ ?y) =>
          match constr:b with
            | false =>
              let e := constr:(not (@Logic.eq _ x y)) in idtac e
            | true =>
              let e := constr:(@Logic.eq _ x y) in idtac e
          end
        | _ => fail 99 "Can't evaluate reified equality properly."
      end.
  Ltac print_model_aux vl vt vs m :=
    match constr:m with
      | List.nil => idtac
      | List.cons (LITINDEX.Atom ?atom,?b) ?Q =>
        let cp := constr:(LITINDEX.lookup vl atom) in
        let p := eval compute [LITINDEX.lookup varmap_find] in cp in
          print_model_aux vl vt vs Q; idtac p " : " b
      | List.cons (LITINDEX.Equation ?s1 ?s2, ?b) ?Q =>
        print_model_aux vl vt vs Q; print_reified_eq vt vs s1 s2 b
    end.  
  Ltac print_model v m :=
    match eval cbv [v] in v with
      | mk_varmaps ?vl ?vt ?vs => 
        let vl := eval cbv [vl] in vl in
        let vt := eval cbv [vt] in vt in
        let vs := eval cbv [vs] in vs in
          print_model_aux vl vt vs m
    end.

  (* THIS IS AN OLD VERSION (< r430) which received model with
     fully computed atoms. We dont use it because it computes the
     original terms and its not convenient. *)
  (* (** This tactic prints a counter model. Note that our [dpll] function *) *)
  (* (*    removes proxies from the counter model since we dont want proxies *) *)
  (* (*    to be shown to the user. *) *)
  (* Ltac print_model m := *)
  (*   match constr:m with *)
  (*     | List.nil => idtac *)
  (*     | List.cons (?proxy,?b) ?Q => *)
  (*       print_model Q; idtac proxy " : " b *)
  (*   end. *)

  (** This tactic builds a single conjunctive formula from
     all the propositional objects in the context. *)
  Ltac conj_context final cur tmp :=
    match goal with
      | H : ?X, final : cur |- _ =>
        match type of X with
          | Prop =>
            let new := constr:(X /\ cur) in
              assert (tmp : new); [exact (conj H final) |];
                clear final; clear H;
                  assert (final : new); [exact tmp |];
                    clear tmp; conj_context final new tmp
          | _ => fail
        end
      | final : cur |- _=> idtac
    end.

  Ltac mintro l := intro l.
  Ltac old_unsat_prepare final :=
    let tmp := fresh "tmp" in
      assert (final : True); [trivial |];
        conj_context final True tmp.
  Ltac unsat_prepare final :=
    build_conjunction final.

  Module Deprecated. (** The following tactics are the old version,
                        they will fail at CNF conversion because of
                        the typing constraint. *)
  (** The tactic [cnfize] applies the lazy CNF conversion 
     lemma to our context formula. *)
  Ltac cnfize final reif :=
    match goal with
      | final : finterp ?v ?form |- _ => 
        set (reif := form) in final;
        apply (F.Conversion.cnf v reif);
          let n := fresh "N" in intro n; 
            DoubleNegUtils.crewrite n final
    end.

  (** Finally, [proof_search] prepares the goal, applies the CNF 
     conversion lemma and the validity theorem in order to transform
     the goal in a simple equality of the form [dpll F = Unsat].
     It then calls [vm_compute] and either succeeds if [dpll] returns
     [Unsat], or displays the counter model to the user. *)
  Ltac proof_search prepare :=
    let f := fresh "final" in
    let r := fresh "reified" in
    let v := fresh "_varmaps" in
      prepare f; apply False_rec;
        quote_everything v;
          ((cnfize f r; refine (validity _ v _ f);
            vm_compute; 
              match goal with
                | |- Unsat = Unsat => trivial
                | |- Sat ?M = Unsat =>
                  idtac "The formula in not valid.";
                    idtac "The following countermodel has been found :";
                      print_model v M
(*                       let m := eval vm_compute in (LSet.elements M) in *)
(*                         print_model m v *)
              end
          )
          || idtac "The reified formula does not interpret"
                   " to the original formula ! Please report")
          || idtac "Reification failed ! Please report".

  (** A wrapper with intros, false elimination and a [try solve],
     so that if the tactic does not succeed, it does leave the 
     context unchanged. 

     This [unsat] tactic is the one that should be called directly
     by a user. 
     *)
  Ltac old_unsat :=
    try solve [
      intros; apply False_rec;
        proof_search unsat_prepare].
  End Deprecated.

  Ltac new_proof_search :=
    let f := fresh "final" in
    let ft := fresh "finalt" in
    let r := fresh "reif" in
    let vm := fresh "vm" in
  (* first we build the conjunction of the formulas in the context *)
      build_conjunction final;
  (* then we reify this formula *)
      ((ergo_reify final r vm;      
        let t := type of f in set (ft := t) in *;
  (* we apply the validity theorem to try and prove our goal *)
          refine (validity' r ft vm _ _ f);
  (* first we check that the reified formula corresponds to the goal *)
          [idtac |
            (vm_compute; change (Some ft = Some ft); reflexivity) || 
              fail 99 "The reify formula does not interpret to "
                      "the original formula. Please report."];
  (* and finally we execute the procedure to check that it returns Unsat *)
  vm_compute;
  match goal with
    | |- Unsat = Unsat => trivial
    | |- Sat ?M = Unsat =>
      (idtac "The formula in not valid.";
        idtac "The following countermodel has been found :";
          print_model vm M)
  end  
                      )
       || fail 99 "Building initial problem failed. Please report").

  Ltac unsat :=
    try solve [intros; apply False_rec; new_proof_search].

  (** A version for proving valid formulas : it uses double negation
     if Classical was imported, otherwise fails with a comprehensive
     error message. *)
  Ltac valid :=
    try solve [intros; 
      match goal with
        |- ~ ?F => intro; new_proof_search
        | _ => valid_prepare; intro; new_proof_search
      end].
End LoadTactic.