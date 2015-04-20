(** This file defines the module type of formulas in clause form. *)
Require Export Containers.Sets.
Require Import Literal Semantics.

(** * The module type [CNF] *)
Module Type CNF.

  (** The module type [CNF] comes with an abstract type for 
     general formulas. This type [formula] can be thought as 
     all the formulas that this module can handle.     *)
  Parameter formula : Type.

  (** The module also brings its own literals, which goes with
     sets and sets of sets of literals.
     *)
  Declare Module L : LITERAL.
  Notation lset := L.lset.
  Notation clause := L.clause.
  Notation cset := L.cset.

  (** The [CNF] instance shall provide a "CNF conversion" function
     that takes a [formula] and returns a sets of clauses.
     Such a formalization (having the module bringing its own abstract
     type of formulas and conversion function) allows instances that
     only accept formulas that are already in CNF, and where [make]
     is just the identity function (see [CNFCONCRETE] for an example).
     *)
  Parameter make : formula -> cset.

  (** In order to convert the result of [L.expand] into a CNF, we
     require a function that builds a [CSet.t] out of a list of lists
     of literals. It is actually totally specified by [cfl_1] but
     depending on the internal representation of finite sets, 
     there may be more efficient way to implement [cfl] than 
     the expression in [cfl_1].
     *)
  Parameter cfl : list (list L.t) -> cset.
  Axiom cfl_1 : 
    forall ll, (cfl ll) [=]
      (fold_right (fun l (cl : cset) => add (fold_right add {} l) cl) {} ll).
  
  (** We also require a function that picks any literal
     in a problem. The way this literal is chosen does not have any
     impact on the properties of the algorithm but allows the user to
     add any heuristic of his own. *)
  Parameter pick : cset -> option (clause * L.t).
  Axiom pick_1 :
    forall (D : cset) (C : clause) (l : L.t), 
      pick D = Some (C, l) -> C \In D /\ l \In C.
  Axiom pick_2 : 
    forall (D : cset),
      (forall C, C \In D -> ~Empty C) -> 
      pick D = None -> Empty D.

  (** The [CNF] module finally brings semantics about its 
     literals and formulas. *)
  Declare Module  Sem : SEM_INTERFACE L.
End CNF.
