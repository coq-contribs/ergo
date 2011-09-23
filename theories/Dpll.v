(** This module defines the interface for reflexive DPLL solvers. *)
Require Export Cnf Semantics Env Sat.

(** * The module type [DPLL] *)
Module Type DPLL (Import F : CNF).
  Declare Module Export E : ENV_INTERFACE F.
  
  Inductive Res : Type :=
    Sat : E.t -> Res
  | Unsat.

  Parameter dpll : F.formula -> Res.
  Axiom dpll_correct :
    forall Pb, dpll Pb = Unsat -> 
      F.Sem.incompatible {} (F.make Pb).
End DPLL.