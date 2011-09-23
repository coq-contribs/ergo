Require Import AltErgo.

(** Examples using [dpll] *)
Require Import GeneratorsNG.
Theorem hole2 : hole 2.
  cbv -[not].
  Time dpll.
Qed.
Theorem hole2_tauto : hole 2.
  cbv -[not].
  Time tauto.
Qed.

Require Import Counting.
Size hole2.
Size hole2_tauto.
Print hole2.
Print hole2_tauto.

Theorem hole3 : hole 3.
  cbv -[not].
  intros.
  Time dplln.
Qed.
Size hole3.
(* hole3_tauto times/mems out *)
Theorem hole4 : hole 4.
  cbv -[not].
  Time dplln.
Qed.
Size hole4.
Theorem hole5 : hole 5.
  cbv -[not].
  Time dplln.
Qed.
Size hole5.

Theorem deb1 : de_bruijn 1.
  cbv -[not iff].
  Time dplln.
Qed.
Size deb1. (* 138, 375 *)
Theorem deb2 : de_bruijn 2.
  cbv -[not iff].
  Time dplln.
Qed.
Size deb2. (* 194, 1337 *)
Theorem deb3 : de_bruijn 3.
  cbv -[not iff].
  Time dplln.
Qed.
Size deb3. (* 252, 4685 *)
Theorem deb4 : de_bruijn 4.
  cbv -[not iff].
  Time dplln.
Qed.
Size deb4. (* 312, 17385 *)
Theorem deb5 : de_bruijn 5.
  cbv -[not iff].
  Time dplln.
Qed.
Size deb5. (* 372, 67301 *)
Theorem deb6 : de_bruijn 6.
  cbv -[not iff].
  Time dplln.
Qed. (* 138 s *)
Size deb6. (* 432, 265889 *)
Theorem deb15 : de_bruijn 15.
  cbv -[not iff].
  Time dplln.
Qed.
Size deb15.
Theorem deb20 : de_bruijn 20.
  cbv -[not iff].
  Time dplln.
Qed.
Size deb20.
Theorem deb100 : de_bruijn 100.
  cbv -[not iff].
  Time dplln.
Qed.
Size deb100.

(** No logicians were harmed during the proof search  :-) *)
Let all := (hole2, hole4, deb20).
Print Assumptions all.

Theorem peirce_or_is_it :
  forall (A B : Prop), ((A -> B) -> B) -> ~A -> False.
Proof.
  dpll.
Abort.

(* (** About valid formulas *) *)
(* Module WithClassic. *)
(*   Theorem vhole2 : vhole 2. *)
(*     cbv -[not]. *)
(*     Require Classical. *)
(*     vdpll. *)
(*   Qed. *)
(*   Print Assumptions vhole2. *)
(* End WithClassic. *)

(** Examples using [cc] *)
Theorem simple_congr  :
  forall (x : nat) (b : bool) (f : nat -> bool), 
    1 = x -> f x = b -> f 1 <> b -> False.
Proof.
  cc.
Qed.
Print simple_congr.
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
  Time cc.
Qed.
Size melange_cc_sat.

Definition FP n m k := 
  forall f, (f^n) 0 = 0 -> (f^m) 0 = 0 -> (f^k) 0 <> 0 -> False.
Theorem FP5_3_1 : FP 5 3 1.
Proof.
  cbv.
  Time cc.
Qed.
Size FP5_3_1. (* 324, 242 *)
Theorem FP13_5_8 : FP 13 5 8.
Proof.
  cbv.
  Time cc.
Qed.
Size FP13_5_8. (* 537, 707 *)
Theorem FP13_5_3 : FP 13 5 3.
Proof.
  cbv.
  Time cc.
Qed.
Size FP13_5_3. (* 472, 662 *)
Theorem FP13_5_2 : FP 13 5 2.
Proof.
  cbv.
  Time cc.
Qed.
Size FP13_5_2. (* 459, 851 *)
Theorem FP13_5_1 : FP 13 5 1.
Proof.
  cbv.
  Time cc.
Qed.
Size FP13_5_1. (* 446, 1475 *)
Theorem FP13_12_1 : FP 13 12 1.
Proof.
  cbv.
  Time cc.
Qed.
Size FP13_12_1. (* 537, 192 *)
Theorem FP13_2_1 : FP 13 2 1.
Proof.
  cbv.
  Time cc.
Qed.
Size FP13_2_1. (* 407, 882 *)
Theorem FP9_4_1 : FP 9 4 1.
Proof.
  cbv.
  Time cc.
Qed.
Size FP9_4_1. (* 385, 390 *)

Theorem FP25_2_1 : FP 25 2 1.
Proof.
  cbv.
  Time cc.
Qed.
Size FP25_2_1. (* 551, 2280 *)
Theorem FP25_11_1 : FP 25 11 1.
Proof.
  cbv.
  Time cc.
Qed.
Size FP25_11_1. (* 668, 14848 *)
Theorem FP25_13_1 : FP 25 13 1.
Proof.
  cbv.
  Time cc.
Qed.
Size FP25_13_1. (* 694, 1722 *)
Theorem FP25_15_5 : FP 25 15 5.
Proof.
  cbv.
  Time cc.
Qed.
Size FP25_15_5. (* 772, 1944 *)
Theorem FP25_24_24 : FP 25 24 24.
Proof.
  cbv.
  Time cc.
Qed.
Size FP25_24_24. (* 1136, 121 *)

Theorem pgcd_fix : 
  forall f, (f^13) 0 = 0 -> (f^5) 0 = 0 -> f 0 <> 0 -> False.
Proof.
  simpl.
  Time cc.
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
  cc.
Qed.

Let allcc := (simple_congr, pgcd_fix, pgcd_fix_sat).
Print Assumptions allcc.

Theorem what_if_its_not_valid :
  forall A (a b c : A) (f : A -> A) (g : A -> A),
    a = b -> f b = f c -> b = c -> g a = g c.
Proof.
  cc.
  vcc.
Abort.

(** Examples using [ergo] *)
Require Import ZArith.
Open Scope Z_scope.

Theorem test_arithZ : 
  forall (A : Type) (x : Z) (a : A) (f : Z -> A),
    1 = x -> f (x + 0) = a -> f 1 <> a -> False.
Proof.
  Time ergo.
Qed.
Size test_arithZ.

Theorem test_arith_nat_sat : 
  forall (A : Type) (x : Z) (a : A) (f : Z -> A),
    (1 = x \/ 2 = x + 1) -> f (0 + x) = a -> f 1 <> a -> False.
Proof.
  Time ergo.
Qed.
Size test_arith_nat_sat.

Theorem shankar_01 : 
  forall (f : Z -> Z) (x y : Z),
    f (x-1) - 1 = x + 1 -> f y + 1 = y - 1 -> y + 1 = x -> False.
Proof.
  intros.
  Time ergo.
Qed.
Size shankar_01.

Fixpoint powerZ (f : Z -> Z) (n : nat) (x : Z) :=
  match n with O => x | S n0 => powerZ f n0 (f x + 0) end.
Notation "f ^Z n" := (powerZ f n)(at level 30).

Theorem pgcd_fix_Z : 
  forall f, (f^Z 13) 0 = 0 -> (f^Z 5) 0 = 0 -> f 0 <> 0 -> False.
Proof.
  simpl.
  Time ergo.
Qed.
Size pgcd_fix_Z.

Let allfull := (test_arithZ, test_arith_nat_sat, pgcd_fix_Z).
Print Assumptions allfull.

Require Import Classical.
Theorem chap10 :
  forall (f : Z -> Z) t0 t1 t2 t3 a,
    t1 = t0 + a -> t2 = t1 + a -> 
    ~(t3 <> t2 + a \/ 2 * a - 1 <> a) ->
    (f(f(f (t3 - 3))) = t0 \/ f(t1 - 1) = t2 - 2) ->
    f(f t0) = t3 - 3 -> f t0 = t0.
Proof.
  intros.
  Time ergo.
  Time vergo.
Qed.
Size chap10.

Module Chap11.
  Theorem peirce : forall (A B : Prop), ((A -> B) -> A) -> ~A -> False.
  Proof. dpll. Qed.
  
  Require Import List.
  Lemma In_list : forall a b c, a = b -> In b ((b+1)::c::a::nil).
  Proof.
    vcc.
    simpl.
    vcc.
  Qed.
  Print peirce.

  (** Diamond *)
  Require Import GeneratorsEq.
  Theorem diamond0 : diamond 0.
  Proof.
    cbv.
    Time vcc.
  Qed.    
  Size diamond0. (* 0, 0.004, 1, 1, 158 *)
  Theorem diamond1 : diamond 1.
  Proof.
    cbv.
    Time vcc.
  Qed.    
  Size diamond1. (* 1, 0.02, 4, 5, 451 *)
  Theorem diamond2 : diamond 2.
  Proof.
    cbv.
    Time vcc.
  Qed.    
  Size diamond2. (* 1, 0.04, 7, 9, 790 *)
  Theorem diamond3 : diamond 3.
  Proof.
    cbv.
    Time vcc.
  Qed.    
  Size diamond3. (* 0.08, 1225 *)
  Theorem diamond4 : diamond 4.
  Proof.
    cbv.
    Time vcc.
  Qed.    
  Size diamond4. (* 0.18, 1772 *)
  Theorem diamond5 : diamond 5.
  Proof.
    cbv.
    Time vcc.
  Qed.
  Size diamond5. (* 1, 0.49, 16, 21, 2447 *)
  (* Theorem diamond8 : diamond 8. *)
  (* Proof. *)
  (*   cbv. *)
  (*   Time vcc. *)
  (* Qed. *)
  (* Size diamond8. (* 1, 4.0, 5400 *) *)

  (** FDiamond *)
  Theorem fdiamond0 : forall f, fdiamond f 0.
  Proof.
    cbv.
    Time vcc.
  Qed.    
  Size fdiamond0. (* 0, 0.004, 1, 1, 160 *)
  Theorem fdiamond1 : forall f, fdiamond f 1.
  Proof.
    cbv.
    Time vcc.
  Qed.    
  Size fdiamond1. (* 1, 0.02, 4, 5, 532 *)
  Theorem fdiamond2 : forall f, fdiamond f 2.
  Proof.
    cbv.
    Time vcc.
  Qed.    
  Size fdiamond2. (* 1, 0.56, 7, 9, 915 *)
  Theorem fdiamond3 : forall f, fdiamond f 3.
  Proof.
    cbv.
    Time vcc.
  Qed.    
  Size fdiamond3. (* 0.12, 1398 *)
  Theorem fdiamond4 : forall f, fdiamond f 4.
  Proof.
    cbv.
    Time vcc.
  Qed.    
  Size fdiamond4. (* 1, 0.29, 1997 *)
  Theorem fdiamond5 : forall f, fdiamond f 5.
  Proof.
    cbv.
    Time vcc.
  Qed.
  Size fdiamond5. (* 1, 0.68, 16, 21, 2728 *)

  (** ZDiamond *)
  (* Ltac vergo := intuition omega. *)
  Theorem Zdiamond0 : Zdiamond 0.
  Proof.    
    cbv -[Zplus].
    Time vergo.
  Qed.    
  Size Zdiamond0. (* 0, 0.008, 1, 1, 177 *)
  Theorem Zdiamond1 : Zdiamond 1.
  Proof.
    cbv -[Zplus].
    Time vergo.
  Qed.    
  Size Zdiamond1. (* 1, 0.04, 4, 5, 536 *)
  Theorem Zdiamond2 : Zdiamond 2.
  Proof.
    cbv -[Zplus].
    Time vergo.
  Qed.    
  Size Zdiamond2. (* 1, 0.14, 7, 9, 949 *)
  Theorem Zdiamond3 : Zdiamond 3.
  Proof.
    cbv -[Zplus].
    Time vergo.
  Qed.    
  Size Zdiamond3. (* 1, 0.28, 1458 *)
  Theorem Zdiamond4 : Zdiamond 4.
  Proof.
    cbv -[Zplus].
    Time vergo.
  Qed.    
  Size Zdiamond4. (* 1, 0.68, 2094 *)
  Theorem Zdiamond5 : Zdiamond 5.
  Proof.
    cbv -[Zplus].
    Time vergo.
  Qed.
  Size Zdiamond5. (* 1, 1.6, 2856 *)
  Theorem Zdiamond6 : Zdiamond 6.
  Proof.
    cbv -[Zplus].
    Time vergo.
  Qed.    
  Size Zdiamond6. (* 1, 3.7, 16, 21, 3768 *)
  Theorem Zdiamond7 : Zdiamond 7.
  Proof.
    cbv -[Zplus].
    Time vergo.
  Qed.    
  Size Zdiamond7. (* 1, 8.3, 4846 *)

  (** FiboArith *)
  Theorem FiboA0 : fibo_arith 0.
  Proof.    
    cbv -[Zplus].
    Time vergo.
  Qed.    
  Size FiboA0. (* 0, 0.008, 1, 1, 204 *)
  Theorem FiboA1 : fibo_arith 1.
  Proof.
    cbv -[Zplus].
    Time vergo.
  Qed.    
  Size FiboA1. (* 1, 0.012, 2, 2, 288 *)
  Theorem FiboA2 : fibo_arith 2.
  Proof.
    cbv -[Zplus]; simpl.
    Time vergo.
  Qed.    
  Size FiboA2. (* 2, 0.036, 3, 3, 436 *)
  Theorem FiboA5 : fibo_arith 5.
  Proof.
    cbv -[Zplus]; simpl.
    (* Time omega. (* 0.19, 6177 *) *)
    Time vergo.
  Qed.    
  Size FiboA5. (* 5, 0.12, 6, 6, 1073 *)
  Theorem FiboA10 : fibo_arith 10.
  Proof.
    cbv -[Zplus]; simpl.
    (* Time omega. (* 0.56, 21727 *) *)
    Time vergo.
  Qed.    
  Size FiboA10. (* 10, 0.48, 11, 11, 2976 *)
  Theorem FiboA15 : fibo_arith 15.
  Proof.
    cbv -[Zplus]; simpl.
    (* Time omega. (* 1.68, 41780 *) *)
    Time vergo.
  Qed.    
  Size FiboA15. (* 15, 1.35, 16, 16, 6259 *)
  Theorem FiboA20 : fibo_arith 20.
  Proof.
    cbv -[Zplus]; simpl.
    (* Time omega. (* 4.0, 68895 *) *)
    Time vergo.
  Qed.
  Size FiboA20. (* 20, 3.14, 21, 21, 11323 *)
End Chap11.