Require Import Quote Ergo Setoid List.
Require Import Semantics Sat Env Dpll SatCaml.
Require Import LLazy CNFLazy CNFLazyN CCX EnvLazy TacticLazy.

(** Instantiates DPLL and loads tactic for given Env *)
Module MakeErgo (_E : ENV_INTERFACE CNFLAZYN).
  Module DPLL.
    Module E := _E.
    Include (SATCAML CNFLAZYN E).
  End DPLL.
  Include TacticLazy.LoadTactic CNFLAZYN DPLL.
End MakeErgo.

(** An environment for propositional literals ... *)
Module EnvSat := ENV CNFLAZYN.
(** ... and the corresponding procedure and tactic. *)
Module ErgoSat := MakeErgo EnvSat.
Ltac ergosat := ErgoSat.unsat.

(** Examples using [ergosat] *)
Require Import Generators.
Theorem hole2 : hole 2 -> False.
  cbv -[not].
  Time ergosat.
Qed.

Theorem hole2_tauto : hole 2 -> False.
  cbv -[not].
  Time tauto.
Qed.

Require Import Counting.
Size hole2.
Size hole2_tauto.
Print hole2.
Print hole2_tauto.

Theorem hole4 : hole 4 -> False.
  cbv -[not].
  Time ergosat.
Qed.
Size hole4.

Theorem deb20 : ~de_bruijn 20 -> False.
  cbv -[not iff].
  Time ergosat.
Qed.
Size deb20.
Print deb20.

(** No logicians were harmed during the proof search  :-) *)
Let all := (hole2, hole4, deb20).
Print Assumptions all.

Theorem peirce_or_is_it :
  forall (A B : Prop), ((A -> B) -> B) -> ~A -> False.
Proof.
  ergosat.
Abort.

(** About valid formulas *)
Module WithClassic.
  Theorem vhole2 : vhole 2.
    cbv -[not].
    Require Import Classical.
    ErgoSat.valid.
  Qed.
  Print Assumptions vhole2.
End WithClassic.

(** An environment for congruence closure with an empty theory *)
Module CCE := CCX.CCX Theory.EmptyTheory.
Module EnvCC := ENVLAZY CNFLAZYN CCE.
(** ... and the corresponding procedure and tactic. *)
Module ErgoCC := MakeErgo EnvCC.
Ltac ergocc := ErgoCC.unsat.

(** Examples using [ergocc] *)
Theorem simple_congr  :
  forall (x : nat) (b : bool) (f : nat -> bool), 
    1 = x -> f x = b -> f 1 <> b -> False.
Proof.
  ergocc.
Qed.
Size simple_congr.
Print simple_congr.

Theorem simple_congr_congruence :
  forall (x : nat) (b : bool) (f : nat -> bool), 
    1 = x -> f x = b -> f 1 <> b -> False.
Proof.
  congruence.
Qed.
Size simple_congr_congruence.
Print simple_congr_congruence.

Fixpoint power (f : nat -> nat) (n x : nat) :=
  match n with 0 => x | S n0 => power f n0 (f x) end.
Notation "f ^ n" := (power f n).

Theorem melange_cc_sat : 
  forall f y, (f (f 0) = y /\ f (f (f y)) = 0) ->
    (f y = 0 \/ f 0 = 0) -> f 0 <> 0 -> False.
Proof.
  simpl.
  Time ergocc.
Qed.
Size melange_cc_sat.

Theorem pgcd_fix : 
  forall f, (f^13) 0 = 0 -> (f^5) 0 = 0 -> f 0 <> 0 -> False.
Proof.
  simpl.
  Time ergocc.
Qed.
Size pgcd_fix.

Theorem pgcd_fix_congruence : 
  forall f, (f^13) 0 = 0 -> (f^5) 0 = 0 -> f 0 <> 0 -> False.
Proof.
  simpl.
  Time congruence.
Qed.
Size pgcd_fix_congruence.

Theorem pgcd_fix_sat :
  forall f, 
    ((f^11) 0 = 0 \/ (f^13) 0 = 0) /\
    ((f^6) 0 = 0 \/ (f^5) 0 = 0) -> f 0 <> 0 -> False.
Proof.
  simpl.
  try congruence.
  ergocc.
Qed.

Let allcc := (simple_congr, pgcd_fix, pgcd_fix_sat).
Print Assumptions allcc.

Theorem what_if_its_not_valid :
  forall A (a b c : A), a = b -> b = c -> a = c -> False.
Proof.
  ergocc.
Abort.

(** An environment for congruence closure with linear arithmetic *)
Module CCA := CCX.CCX TheoryArith.ArithTheory.
Module EnvCCA := ENVLAZY CNFLAZYN CCA.
(** ... and the corresponding procedure and tactic. *)
Module ErgoCCA := MakeErgo EnvCCA.
Ltac ergofull := ErgoCCA.unsat.

(** Examples using [ergofull] *)
Require Import ZArith.
Open Scope Z_scope.

Theorem test_arithZ : 
  forall (A : Type) (x : Z) (a : A) (f : Z -> A),
    1 = x -> f (x + 0) = a -> f 1 <> a -> False.
Proof.
  Time ergofull.
Qed.
Size test_arithZ.

Theorem test_arith_nat_sat : 
  forall (A : Type) (x : Z) (a : A) (f : Z -> A),
    (1 = x \/ 2 = x + 1) -> f (0 + x) = a -> f 1 <> a -> False.
Proof.
  Time ergofull.
Qed.
Size test_arith_nat_sat.

Theorem shankar_01 : 
  forall (f : Z -> Z) (x y : Z),
    f (x-1) - 1 = x + 1 -> f y + 1 = y - 1 -> y + 1 = x -> False.
Proof.
  intros.
  Time ergofull.
Qed.
Size shankar_01.

Fixpoint powerZ (f : Z -> Z) (n : nat) (x : Z) :=
  match n with O => x | S n0 => powerZ f n0 (f x + 0) end.
Notation "f ^Z n" := (powerZ f n)(at level 30).

Theorem pgcd_fix_Z : 
  forall f, (f^Z 13) 0 = 0 -> (f^Z 5) 0 = 0 -> f 0 <> 0 -> False.
Proof.
  simpl.
  Time ergofull.
Qed.
Size pgcd_fix_Z.

Let allfull := (test_arithZ, test_arith_nat_sat, pgcd_fix_Z).
Print Assumptions allfull.

Theorem chap10 :
  forall (f : Z -> Z) t0 t1 t2 t3 a,
    t1 = t0 + a -> t2 = t1 + a -> 
    ~(t3 <> t2 + a \/ 2 * a - 1 <> a) ->
    (f(f(f (t3 - 3))) = t0 \/ f(t1 - 1) = t2 - 2) ->
    f(f t0) = t3 - 3 -> f t0 <> t0 -> False.
Proof.
  intros.
  Time ergofull.
Qed.
Size chap10.