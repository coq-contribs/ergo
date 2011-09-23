(** This file instantiates our DPLL procedure on
   all available different strategies of CNF conversion,
   providing a whole set of tactics. *)
Require Import Quote Ergo Setoid List.
Require Import Semantics Sat (* Env *) Dpll (* SatStrategy *) SatCaml.
Require Import LLazy CNFLazy CNFLazyN CCX EnvLazy TacticLazy.
(* Require Import LProp CNFConcrete TacticConcrete. *)
(* Require Import CNFAbstract TacticAbstract. *)
(* Require Import TacticTseitin TacticTseitin2. *)
 
(** We introduce a module [K] that contains the excluded-middle. 
   It is a way to encapsulate classical reasoning since [Classical]
   is only imported inside this module. We can then pass this module
   to the functor that require classical reasoning and be sure that
   other tactics do not use the excluded-middle. *)
Module K.
  Require Import Classical.
  Definition classic := classic.
End K.

(** Instantiating the DPLL procedure with efficient strategy
   on all different CNF modules:
   - [CNFCONCRETE] is a module for formulas that are converted
   into CNF before being reified
   - [CNFABSTRACT] is a module for formulas that are converted
   into CNF after being reified
   - [CNFLAZY] is our module of formulas with lazy CNF conversion
   - [CNFLAZYN] is a variant of [CNFLAZY] where the number of 
   proxies is minimized by using n-ary operators
   *)

(* Module MAKESAT (F : Cnf.CNF). *)
(*   Module E := ENV F. *)
(*   Include (SAT F E). *)
(* End MAKESAT. *)
(* Time Module SC := MAKESAT(CNFCONCRETE). *)
(* Time Module SA := MAKESAT(CNFABSTRACT). *)
(* Time Module S := MAKESAT(CNFLAZY). *)
(* Time Module SN := MAKESAT(CNFLAZYN). *)
Module E := ENVLAZY CNFLAZY CCA.
Module EN := ENVLAZY CNFLAZYN CCA.
Module S.
  Module E := E.
  Time Include (SAT CNFLAZY E).
End S.
Module SN.
  Module E := EN.
  Time Include (SAT CNFLAZYN E).
End SN.
(* Module SStrat. *)
(*   Module E := ENV CNFLAZY. *)
(*   Time Include (SATSTRATEGY CNFLAZY E). *)
(* End SStrat. *)
(* Module SStratN. *)
(*   Module E := ENV CNFLAZYN. *)
(*   Time Include (SATSTRATEGY CNFLAZYN E). *)
(* End SStratN. *)
Module SCaml.
  Module E := E.
  Time Include (SATCAML CNFLAZY E).
End SCaml.
Module SCamlN.
  Module E := EN.
  Time Include (SATCAML CNFLAZYN E).
End SCamlN.
  
(** All these DPLL procedures can be passed to functors creating
   the tactics. Some procedures can be used with several different
   tactics constructor, for instance there are two flavours of
   Tseitin-style conversion. 
   - [TacticConcrete] converts formulas through a set of rewriting
   rules, it is the only one requiring classical reasoning
   - [TacticAbstract] converts formulas through naive CNF translation
   - [TacticTseitin] uses standard Tseitin CNF conversion
   - [TacticTseitin2] converts formulas into NNF first and then
   applies Plaisted/Greenbaum CNF conversion
   - [TacticLazy] uses the conversion in [CNFLAZY]
   - [TacticLazyN] uses the conversion in [CNFLAZYN]
*)
(* Time Module TacC := TacticConcrete.LoadTactic(K)(SC). *)
(* Time Module TacA := TacticAbstract.LoadTactic(SA). *)
(* Time Module TacT := TacticTseitin.LoadTactic(SA). *)
(* Time Module TacT2 := TacticTseitin2.LoadTactic(SA). *)
Time Module Tac := TacticLazy.LoadTactic(CNFLAZY)(S).
Time Module TacN := TacticLazy.LoadTactic(CNFLAZYN)(SN).
(* Time Module TacStrat := TacticLazy.LoadTactic(CNFLAZY)(SStrat). *)
(* Time Module TacStratN := TacticLazy.LoadTactic(CNFLAZYN)(SStratN). *)
Time Module TacCaml := TacticLazy.LoadTactic(CNFLAZY)(SCaml).
Time Module TacCamlN := TacticLazy.LoadTactic(CNFLAZYN)(SCamlN).

(** Finally, we give shorter names to all the tactics
   provided by the instantations above. *)
(* Ltac unsatc := TacC.unsat. *)
(* Ltac unsata := TacA.unsat. *)
(* Ltac unsatt := TacT.unsat. *)
(* Ltac unsatt2 := TacT2.unsat. *)
Ltac unsat := Tac.unsat.
Ltac unsatn := TacN.unsat.
(* Ltac unsats := TacStrat.unsat. *)
(* Ltac unsatsn := TacStratN.unsat. *)
Ltac unsatc := TacCaml.unsat.
Ltac unsatcn := TacCamlN.unsat.