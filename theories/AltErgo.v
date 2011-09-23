Time Require Import
  CNFLazy CNFLazyN Env SatCaml 
  Dpll TacticLazy CCX EnvLazy.
Require Export Ergo Quote.

(** Instantiates DPLL and loads tactic for given Env and CNF module *)
Module MakeErgo
  (_F : CNFLAZY_INTERFACE)
  (_E : ENV_INTERFACE _F).
  Module DPLL <: DPLL _F.
    Module E := _E.
    Include (SATCAML _F E).
  End DPLL.
  Include LoadTactic _F DPLL.
End MakeErgo.

(** Environments for empty / cc / cc+arith,
   both for Lazy and LazyN cnf conversion *)
Time Module E := ENV CNFLAZY.
Module EN := ENV CNFLAZYN.
Time Module EnvCC := ENVLAZY CNFLAZY CCE.
Module EnvCCN := ENVLAZY CNFLAZYN CCE. 
Time Module EnvCCA := ENVLAZY CNFLAZY CCA.
Module EnvCCAN := ENVLAZY CNFLAZYN CCA.

(** Instantiates MakeErgo on all environments and gives shortcut
   notations for the tactic. *)
Time Module ErgoE := MakeErgo CNFLAZY E.
Module ErgoEN := MakeErgo CNFLAZYN EN.
Time Module ErgoCC := MakeErgo CNFLAZY EnvCC.
Module ErgoCCN := MakeErgo CNFLAZYN EnvCCN.
Time Module ErgoCCA := MakeErgo CNFLAZY EnvCCA.
Module ErgoCCAN := MakeErgo CNFLAZYN EnvCCAN.

Ltac dpll := ErgoE.unsat.
Ltac dplln := ErgoEN.unsat.
Ltac vdpll := ErgoE.valid.
Ltac vdplln := ErgoEN.valid.
Ltac cc := ErgoCC.unsat.
Ltac ccn := ErgoCCN.unsat.
Ltac vcc := ErgoCC.valid.
Ltac vccn := ErgoCCN.valid.
(* nb: cannot use [Ltac ergo := ...] because the name ergo has been
   reserved by Dp ! Dp should reserve altergo instead. *)
Tactic Notation "ergo" := ErgoCCA.unsat.
Ltac ergon := ErgoCCAN.unsat.
Ltac vergo := ErgoCCA.valid.
Ltac vergon := ErgoCCAN.valid.