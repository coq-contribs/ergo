(** This file contains the common part of the [CNF] modules
   built on top of the module [LLAZY] of lazy literals. *)
Require Import Quote List Ergo.
Require Import BinPos LLazy SemLazy.
Require Import Containers.Sets.
Require Import Cnf Semantics DoubleNegUtils Setoid.

(** * The module type [CNFLAZY_INTERFACE]
   
   This module defines the interface that a [CNF] module working
   with [LLAZY] literals should match. First, we use [Include Type]
   to include the module [L := LLAZY] of literals, and we define
   a formula as simply being a literal [LLAZY.t].
*)
Module Type CNFLAZY_INTERFACE.
(** Doesnt work for some reason... *)
  Include Type CNF
    with Module L := LLAZY
    with Module Sem := SEMLAZY
    with Definition formula := LLAZY.t.

  Axiom make_1 : 
    forall f, make f [=] singleton {f}.

  Definition interp : varmaps -> formula -> Prop
    := LLAZY.interp.

  (** We also require a conversion function [mk_form] that builds
     a formula (a proxy hierarchy) from a concrete reified formula
     of type [Ergo.form]. This conversion should return a semantically 
     equivalent formula, as stated by the axiom [cnf].
     Addendum (May 2010) : we now add a prerequisite on a formula for
     the CNF to be correct, it must be well-typed in the sense of
     [Ergo.well_typed_formula].
     *)
  Module Conversion.
    Parameter mk_form : fform -> formula.
    
    Axiom cnf :
      forall v f, Ergo.well_typed_formula v f -> 
        ~~(finterp v f <-> interp v (mk_form f)).
  End Conversion.
End CNFLAZY_INTERFACE.

(** * The module [CNFLAZYCOMMON]
   
   We also define a module which is the "basis" of all
   modules that match [CNFLAZY_INTERFACE]. Namely, this module
   contains the module of literals, builds the necessary finite
   sets and facts about these sets.
   It also provides the [pick] function used to choose a literal.
   Thanks to this module, we aboid duplication between the different
   variants of [CNFLAZY_INTERFACE] that we will implement.
*)
Module CNFLAZYCOMMON.

  Module Import L := LLAZY.

  Notation lset := (@set L.t L.t_OT (@SetAVLInstance.SetAVL_FSet L.t L.t_OT)).
  Notation clause := (@set L.t L.t_OT 
    (@SetListInstance.SetList_FSet L.t L.t_OT)).

  Definition clause_OT : OrderedType clause := SOT_as_OT.
  Existing Instance clause_OT.
  Notation cset := (@set clause clause_OT 
    (@SetListInstance.SetList_FSet clause clause_OT)).
(*   Module LSet := FSetList.Make(L). *)

(*   Module Clause := FSetList.Make(L). *)
(*   Module CSet := FSetList.Make(Clause). *)
  
(*   Module LFacts := WFacts(Clause). *)
(*   Module CFacts := WFacts(CSet). *)

  Definition formula := L.t.

  (** We provide a function that picks the first literal of a problem. *)
  Definition pick (D : cset) := 
    match choose D with 
      | None => None
      | Some c => 
        match choose c with
          | Some l => Some (c, l)
          | None => None
        end
    end.

  Fact pick_1 :
    forall (D : cset) (C : clause) (l : L.t), 
      pick D = Some (C, l) -> C \In D /\ l \In C.
  Proof.
    intros D c l; unfold pick; case_eq (choose D).
    intros e Hc; case_eq (choose e).
    intros l' Hl' Heq; inversion Heq; subst; split.
    exact (choose_1 Hc). exact (choose_1 Hl').
    intros; discriminate. intros; discriminate.
  Qed.
    
  Fact pick_2 : 
    forall (D : cset),
      (forall C, C \In D -> ~Empty C) ->
      pick D = None -> Empty D.
  Proof.
    intros D HD; unfold pick; case_eq (choose D).
    intros c Hc; case_eq (choose c).
    intros; discriminate.
    intro abs; contradiction 
      (HD c (choose_1 Hc) (choose_2 abs)).
    intros empty _; exact (choose_2 empty).
  Qed.

  (** And the adhoc semantics for literals with equations *)
  Module Sem := SEMLAZY.
End CNFLAZYCOMMON.
