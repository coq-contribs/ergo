(** This file generates unsatisfiable formulas for problems
   in the fragment SAT + EUF or SAT + EUF + ZArith. *)

(** We define families of boolean variables indexed by an integer. *)
Inductive x : nat -> Prop :=
| mk_x : forall i, x i.
Inductive y : nat -> Prop :=
| mk_y : forall i, y i.
Inductive z : nat -> Prop  :=
| mk_z : forall i, z i.

(** [diamond_equations acc n] appends to the formula [acc] all the 
   disjunctions [(x i = y i /\ y i = x (S i)) \/ 
   ((x i = z i) /\ (z i = x (S i))] for [i] ranging [0] to [pred n].
   It corresponds to "diamond" equalities on the chains [x], [y] and [z]:
        y0       y1
      /   \    /    \
   x 0 ----> x 1 -----> .................. ----> x n
      \    /   \    /
        z0       z1
   such that each diamond constraint ensures that [x i = x (S i)] by 
   transitivity whether at the top or the bottom of the diamond.
*)
Fixpoint diamond_equations (acc : Prop) (n : nat) : Prop :=
  match n with
    | O => acc
    | S m => 
      let eq1 := x m = y m /\ y m = x n in
      let eq2 := x m = z m /\ z m = x n in
        diamond_equations ((eq1 \/ eq2) -> acc) m
  end.

(** [diamond n] returns the implication [diamond_equations n -> x 0 = x n].
   It is a valid formula with [1 + 4 * n] equations between [1 + 3 * n]
   variables. *)
Definition diamond (n : nat) : Prop :=
  diamond_equations (x 0 = x n) n.

(** We now implement a variation of [diamond] where one layer of a
   function symbol [f] is added to the [x_i] at every step. Whereas
   [diamond n] is valid in SAT + equivalence, this one requires congruence.

   [fdiamond_equations f acc n] appends to the formula [acc] all the 
   disjunctions [x i = y i /\ y i = f (x (S i)) \/ 
   ((x i = z i) /\ (z i = f (x (S i)))] for [i] ranging [0] to [pred n].
   It corresponds to "diamond" equalities on the chains [x], [y] and [z]:
        y0       y1
      /   \    /    \
   x 0 ---> f(x 1)-----> .................. ----> f^n(x n)
      \    /   \    /
        z0       z1
   such that each diamond constraint ensures that [x i = f(x (S i))] 
   by transitivity whether at the top or the bottom of the diamond.
   NB : it is actually going in reverse order with respect to the above schema
   but you get the idea.
*)
Fixpoint fdiamond_equations (f : Prop -> Prop) (acc : Prop) (n : nat) : Prop :=
  match n with
    | O => acc
    | S m => 
      let eq1 := x m = y m /\ y m = f (x n) in
      let eq2 := x m = z m /\ z m = f (x n) in
        fdiamond_equations f ((eq1 \/ eq2) -> acc) m
  end.

(** [fdiamond n] returns the implication 
   [fdiamond_equations f n -> x 0 = f^n (x n)].
   It is a valid formula with [1 + 4 * n] equations between [1 + 3 * n]
   variables. *)
Fixpoint power (f : Prop -> Prop) n x :=
  match n with 0 => x | S m => power f m (f x) end.
Definition fdiamond (f : Prop -> Prop) (n : nat) : Prop :=
  fdiamond_equations f (x 0 = power f n (x n)) n.

(** We define families of integer variables indexed by an integer. *)
Require Import ZArith.
Parameter zx : nat -> Z.
Parameter zy : nat -> Z.
Parameter zz : nat -> Z.

(** [diamond_Zequations acc n] appends to the formula [acc] all the 
   disjunctions [(x i = y i /\ y i = 1 + x (S i)) \/ 
   ((x i = z i) /\ (z i = 1 + x (S i))] for [i] ranging [0] to [pred n].
   It corresponds to "diamond" equalities on the chains [x], [y] and [z]:
        y0       y1
      /   \    /    \
   x 0 ----> x 1 -----> .................. ----> x n
      \    /   \    /
        z0       z1
   such that each diamond constraint ensures that [x i = 1 + x (S i)] by 
   transitivity whether at the top or the bottom of the diamond.
*)
Fixpoint diamond_Zequations (acc : Prop) (n : nat) : Prop :=
  match n with
    | O => acc
    | S m => 
      let eq1 := zx m = zy m /\ zy m = (1 + zx n)%Z in
      let eq2 := zx m = zz m /\ zz m = (1 + zx n)%Z in
        diamond_Zequations ((eq1 \/ eq2) -> acc) m
  end.

(** [Zdiamond n] returns the implication 
   [diamond_Zequations n -> zx 0 - n = zx n].
   It is a valid formula with [1 + 4 * n] equations between [1 + 3 * n]
   variables. *)
Definition Zdiamond (n : nat) : Prop :=
  diamond_Zequations (zx 0 - (Z_of_nat n) = zx n)%Z n.


(** Another goal which only contains arithmetic, no real congruence, 
   and basically no propositional value. It is a sequence of arithmetic
   equalities which simulate the definition of a Fibonacci number.
   *)
Fixpoint fibo_defs (res : Prop) (n : nat)  : Prop :=
  match n with
    | 0 => zx 0 = 1%Z -> res
    | S m =>
      match m with 
        | 0 => zx 1 = zx 0 -> fibo_defs res m
        | S p => zx (S (S p)) = Zplus (zx (S p)) (zx p) -> fibo_defs res m
      end
  end.
Fixpoint fibo (n : nat) (z : Z) : Z :=
  match n with
    | 0 => 1%Z
    | S m =>
      match m with
        | 0 => 1%Z
        | S p => Zplus (fibo p (z-2)) (fibo m (z-1))
      end
  end.
Definition fibo_arith (n : nat) :=
  fibo_defs (zx n = fibo n (Z_of_nat n)) n.