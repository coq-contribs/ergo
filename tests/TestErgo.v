Require Import Ergo.

(* Testing build_conjunction *)
Goal forall (A B C : Prop), A -> B -> C -> A.
  build_conjunction final.
  Check final.
  intros.
  build_conjunction final2.
  Check final2.
  tauto.
Defined.
Print Unnamed_thm.

(* Testing reification *)
Goal forall (A B C : Prop), A -> B -> C -> A.
  intros.
  build_conjunction final.
  ergo_reify final reif v.
Abort.

Goal forall (A : Prop) (x : nat) (f : nat -> Prop),
  x = 3 -> f (x + x - 5) = A -> False.
  intros.
  build_conjunction final.
  ergo_reify final reif v.
Abort.

Require Import ZArith.
Goal forall (A : Prop) (x : Z) (f : Z -> Z),
  f x = 3%Z -> A -> False.
  intros.
  build_conjunction final.
  ergo_reify final reif v.
Abort.

Goal forall (A : Prop) (x : N) (f : N -> Prop),
  x = 3%N -> f (x + x - 5)%N = A -> False.
  intros.
  build_conjunction final.
  ergo_reify final reif v.
Abort.

Goal forall (A : Prop) (x : positive) (f : positive -> Prop),
  x = 3%positive -> f (x + x - 5)%positive = A -> False.
  intros.
  build_conjunction final.
  ergo_reify final reif v.
Abort.

(* Testing [valid_prepare] *)
Require Import Classical.
Goal forall A, ~~A -> A.
  intro; valid_prepare.
Abort.