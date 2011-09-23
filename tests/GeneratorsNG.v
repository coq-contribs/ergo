(** This file generates unsatisfiable formulas for problems
   commonly used to benchmark SAT solving procedures. *)

Require Import List.
Fixpoint introduce_vars 
  (P : list Prop -> Prop) (acc : list Prop) (n : nat) :=
  match n with
    | 0 => P (rev acc)
    | S m => forall (x : Prop), introduce_vars P (x::acc) m
  end.
Eval vm_compute in introduce_vars (fun l => l = l) nil 12.

(** * Pigeon hole formulas 
   
   The pigeon hole formula with [n] holes, [hole(n)], states that
   there is no way to put [n+1] pigeons in [n] different holes such
   that no two pigeons occupy the same hole. In its valid version,
   it states that if [n+1] pigeons are in [n] different holes, at
   least one hole contains two of them pigeons.
*)

Section HoleWithListVars.
  Variable vars : list Prop.
  Variable N : nat.

  (** We define a propositional predicate [occ i j] which denotes
     the fact that the pigeon [i] occupies the hole [j]. 
     *)
  Definition occ (i j : nat) : Prop :=
    nth (i * N + j) vars True.

  (** The next definition, [is_home p n] builds a formula expressing
     that the pigeon [p] is at least in one of the holes 0 to [n].
     *)
  Fixpoint is_home (p n : nat) : Prop :=
    match n with
      | O => occ p O
      | S n0 => occ p n \/ is_home p n0
    end.

  (** We can now build a conjunction expressing that all pigeons 
     number 0 to [n+1] have safely found home in the holes 0 to [n]. 
     *)
  Fixpoint everyone_home_aux (n : nat) (p : nat) : Prop :=
    match p with
      | O => is_home O n
      | S p0 => is_home p n /\ everyone_home_aux n p0
    end.
  Definition everyone_home (n : nat) : Prop :=
    everyone_home_aux n (S n).

  (** This wraps up the first part of the pigeon hole formula. For the
     second part, we need to express that for every hole [h], there 
     mustn't be two different pigeons [i] and [j] such that
     [occ i h] and [occ j h] both stand.
     We start by a quick definition for this very last part, two pigeons
     are said to be "safe" with respect to a hole if at least one of them
     is not in the hole.
     *)
  Definition safe (h : nat) (i j : nat) :=
    ~occ i h \/ ~occ j h.

  (** Given a hole [h], we need a formula that says that all possible
     pairs of pigeons are safe wrt that hole. Such a hole is called 
     "sane", and for efficiency reasons, we try to express every
     pair of pigeon only once, by only adding a clause [safe h i j]
     when [i < j].
     *)
  Fixpoint sane_aux_2 (h : nat) (p p' : nat) : Prop :=
    match p' with
      | O => safe h p O
      | S p'0 => safe h p p' /\ sane_aux_2 h p p'0
    end.
  Fixpoint sane_aux (h : nat) (p : nat) : Prop :=
    match p with
      | O => True (* unused, but correct nonetheless *)
      | 1 => safe h 1 0
      | S p0 => sane_aux_2 h p p0 /\ sane_aux h p0
    end.
  Definition sane (h : nat) (n : nat) : Prop :=
    sane_aux h (S n).

  (** Finally, everyone is a happy pigeon when all holes are sane,
     because it is well known that pigeons hate living in crowded areas. 
     *)
  Fixpoint everyone_happy_aux (n : nat) (h : nat) : Prop :=
    match h with
      | O => sane O n
      | S h0 => sane h n /\ everyone_happy_aux n h0
    end.
  Definition everyone_happy (n : nat) : Prop :=
    everyone_happy_aux n n.
End HoleWithListVars.
(** Now, we have everything we need to express the pigeon hole
   formulas [hole n], which is true if and only if [n+1] pigeons
   can live happily in [n] holes.
   Note that up to this point, for practical reasons, we have
   indexed pigeons and holes starting with 0. This means, for instance,
   that the formula [everyone_happy n] actually ensures the sanity 
   property for [n+2] pigeons and [n+1] holes.
   [hole] compensates for that by treating 0 as a special case (which
   is of course [False] since there's no way a single pigeon will be
   happy without at least one hole to live in).
   *)
Definition hole (n : nat) : Prop :=
  match n with
    | O => False
    | S n0 => 
      introduce_vars (fun l =>
        (everyone_home l n n0 /\ everyone_happy l n n0) -> False)
      nil (S n * n)
  end.

(** A couple of examples of pigeon hole formulas for small values of [n].
   Note that the size of the formula increases in [n] squared.
*)
Section Example.
  Definition hole1 := hole 1.
  Time Eval cbv -[not] in hole1.

  Definition hole2 := hole 2.
  Time Eval cbv -[not] in hole2.

  Definition hole6 := hole 6.
  Time Eval cbv -[not] in hole6.

  Definition hole10 := hole 10.
  Time Eval cbv -[not] in hole10.
End Example.

(* (** * Pigeon hole formulas (revisited) *)
   
(*    We now turn to another possible definition of the pigeon hole  *)
(*    formulas, expressed in their valid flavour. The real difference *)
(*    with the previous version is that the unsatisfiable version *)
(*    was naturally expressed in CNF, whereas this one will not be *)
(*    a CNF formula. Therefore it will stress the CNF conversion  *)
(*    mechanism a little more. *)

(*    We use the same family of variables [occ i j] of course. *)
(* *) *)

(* (** The first part of the formula expresses once again the fact *)
(*    that every pigeon is in a hole, so we will reuse the [everyone_home] *)
(*    function that we defined above. *)
(*    The second part expresses that there is at least one hole with *)
(*    two pigeons in it. We start by defining this last notion, ie. the *)
(*    fact that two pigeons live in the same hole. *)
(*    *) *)
(* Definition room_mate (h : nat) (i j : nat) := *)
(*   occ i h /\ occ j h. *)

(* (** Given a particular hole [h], the next formula expresses how *)
(*    at least one pair of pigeon are room mates in this hole. *)
(*    Such a hole is said to be "crowded". *)
(*    As before, we make sure we only add each pair of pigeon once. *)
(* *) *)
(* Fixpoint crowded_aux_2 (h : nat) (p p' : nat) : Prop := *)
(*   match p' with *)
(*     | O => room_mate h p O *)
(*     | S p'0 => room_mate h p p' \/ crowded_aux_2 h p p'0 *)
(*   end. *)
(* Fixpoint crowded_aux (h : nat) (p : nat) : Prop := *)
(*   match p with *)
(*     | O => False (* unused, but correct nonetheless *) *)
(*     | 1 => room_mate h 1 0 *)
(*     | S p0 => crowded_aux_2 h p p0 \/ crowded_aux h p0 *)
(*   end. *)
(* Definition crowded (h : nat) (n : nat) : Prop := *)
(*   crowded_aux h (S n). *)

(* (** Now, we are left to define a formula stating that at least *)
(*    one hole must be crowded, which is a simple disjunction over *)
(*    all possible holes.  *)
(* *) *)
(* Fixpoint one_is_crowded_aux (n : nat) (h : nat) : Prop := *)
(*   match h with *)
(*     | O => crowded O n *)
(*     | S h0 => crowded h n \/ one_is_crowded_aux n h0 *)
(*   end. *)
(* Definition one_is_crowded (n : nat) : Prop := *)
(*   one_is_crowded_aux n n. *)

(* (** Finally, a valid formula expressing the pigeon hole problem *)
(*    is just the following implication : *)
(* *) *)
(* Definition vhole (n : nat) : Prop := *)
(*   match n with *)
(*     | O => True *)
(*     | S n0 =>  *)
(*       everyone_home n0 -> one_is_crowded n0 *)
(*   end. *)

(* (** Again, a couple of examples. *) *)
(* Section VExample. *)
(*   Definition vhole1 := vhole 1. *)
(*   Time Eval cbv -[not] in vhole1. *)

(*   Definition vhole2 := vhole 2. *)
(*   Time Eval cbv -[not] in vhole2. *)

(*   Definition vhole6 := vhole 6. *)
(*   Time Eval cbv -[not] in vhole6. *)

(*   Definition vhole10 := vhole 10. *)
(*   Time Eval cbv -[not] in vhole10. *)
(* End VExample. *)

(** * De Bruijn formula

   The De Bruijn formula with parameter [n] states that among [2n+1] boolean
   variables set in a circular list, at least two adjacent variables are
   equal.
*)
Require Import Arith.
Section WithListVars.
  Variable variables : list Prop.

  Definition x i := nth i variables True.

  (** When the parameter of the problem is [n], variables should be indexed *)
(*      modulo [2n+1], starting at 0. For that reason, we define what it means  *)
(*      for two adjacent variables to be equal and we include a special case *)
(*      for the first and last variables. *)
  Definition equals (n : nat) (i : nat) : Prop :=
    match i with
      | O => x O <-> x (n+n)
      | S i0 => x i <-> x i0
    end.

  (** Now, the formula we want is simply a big disjunction expressing that *)
(*      there must be an equivalence between [var n i] and [var n (S i)] for *)
(*      at least one [i] between 0 and [2*n].  *)
(*      *)
  Fixpoint some_are_equal (n : nat) (i : nat) :=
    match i with
      | O => equals n O
      | S i0 => equals n i \/ some_are_equal n i0
    end.
End WithListVars.
Definition de_bruijn (n : nat) : Prop :=
  introduce_vars (fun l => ~(some_are_equal l n (n+n)) -> False) 
  nil (S (n+n)).

(** A couple of examples for De Bruijn formulas.  *)
(*    Unlike pigeon hole formulas, these De Bruijn formulas grow *)
(*    linearly with the parameter [n]. *)
(*    *)
Section DBExample.
  Definition deb1 := de_bruijn 1.
  Time Eval cbv -[not iff] in deb1.

  Definition deb2 := de_bruijn 2.
  Time Eval cbv -[not iff] in deb2.

  Definition deb6 := de_bruijn 6.
  Time Eval cbv -[not iff] in deb6.

  Definition deb10 := de_bruijn 10.
  Time Eval cbv -[not iff] in deb10.

  Definition deb50 := de_bruijn 50.
  Time Eval cbv -[not iff] in deb50.
End DBExample.

(* (** * De Bruijn formula (in 2-SAT CNF) *)

(*    We redefine the De Bruijn formula, this time such that the resulting *)
(*    formula in not only in CNF, but also in the 2-SAT fragment. It will *)
(*    be unsatisfiable, whereas the above formula was valid. *)
(* *) *)
(* Check x. *)
(* Inductive x (i : nat) : Prop := *)
(* | mk_x : x i. *)

(* (** Conversely to what we did above, we define what it means for two *)
(*    adjacent variables to be different. We again deal with the special  *)
(*    case for the first and last variables. *) *)
(* Definition differs (n : nat) (i : nat) : Prop := *)
(*   match i with  *)
(*     | O =>  *)
(*       let n2 := n+n in (x O \/ x n2) /\ (~x 0 \/ ~x n2) *)
(*     | S i0 => (x i \/ x i0) /\ (~x i \/ ~x i0) *)
(*   end. *)

(* (** Now, the formula we want is simply a big conjunction expressing that *)
(*    all adjacent variables must differ.  *)
(*    *) *)
(* Fixpoint all_variables_differ (n : nat) (i : nat) := *)
(*   match i with *)
(*     | O => differs n O *)
(*     | S i0 => differs n i /\ all_variables_differ n i0 *)
(*   end. *)
(* Definition ude_bruijn (n : nat) : Prop := *)
(*   all_variables_differ n (n+n). *)

(* (** The same examples for the unsatisfiable 2-SAT version *)
(*    of the De Bruijn formulas.  *)
(*    *) *)
(* Section DBExample2. *)
(*   Definition udeb1 := ude_bruijn 1. *)
(*   Time Eval cbv -[not iff] in udeb1. *)

(*   Definition udeb2 := ude_bruijn 2. *)
(*   Time Eval cbv -[not iff] in udeb2. *)

(*   Definition udeb6 := ude_bruijn 6. *)
(*   Time Eval cbv -[not iff] in udeb6. *)

(*   Definition udeb10 := ude_bruijn 10. *)
(*   Time Eval cbv -[not iff] in udeb10. *)

(*   Definition udeb50 := ude_bruijn 50. *)
(*   Time Eval cbv -[not iff] in udeb50. *)
(* End DBExample2. *)

(* (** * Associativity of equivalences  *)

(*    The formula [equivn n] has the form : *)
(*    [(a1 <-> (a2 <-> (.... an))) <-> (((a1 <-> a2) <-> ...) <-> an)] *)
(*    and is valid. *)
(* *) *)
(* Inductive a : nat -> Prop := *)
(* | mk_a : forall i, a i. *)

(* Fixpoint Ln (n : nat) := *)
(*   match n with *)
(*     | O => a 0 *)
(*     | S n0 => Ln n0 <-> a n *)
(*   end. *)
(* Fixpoint Rn (n : nat) := *)
(*   match n with *)
(*     | O => a 0 *)
(*     | S n0 => a n <-> Rn n0 *)
(*   end. *)
(* Definition equivn (n : nat) := *)
(*   Ln n <-> Rn n. *)

(* Section EquivExample. *)
(*   Definition equiv1 := equivn 1. *)
(*   Time Eval cbv -[not iff] in equiv1. *)

(*   Definition equiv2 := equivn 2. *)
(*   Time Eval cbv -[not iff] in equiv2. *)

(*   Definition equiv10 := equivn 10. *)
(*   Time Eval cbv -[not iff] in equiv10. *)

(*   Definition equiv30 := equivn 30. *)
(*   Time Eval cbv -[not iff] in equiv30. *)
(* End EquivExample. *)

(* (** * Franzen formulas  *)

(*    The Franzen formula with parameter [n] has the following form : *)
(*    [(~a0 \/ ~a1 .... \/ ~an) \/ (a0 /\ a1 /\ ... /\ an)]. *)
(*    It is valid since it means that at least one variable is false, *)
(*    or they are all true. *)
(* *) *)
(* Fixpoint one_is_false (n : nat) := *)
(*   match n with *)
(*     | O => ~a O *)
(*     | S n0 => one_is_false n0 \/ ~a n *)
(*   end. *)

(* Fixpoint all_are_true (n : nat) := *)
(*   match n with *)
(*     | O => a O *)
(*     | S n0 => all_are_true n0 /\ a n *)
(*   end. *)

(* Definition Fn (n : nat) :=  *)
(*   one_is_false n \/ all_are_true n. *)

(* Section FExample. *)
(*   Definition f1 := Fn 1. *)
(*   Time Eval cbv -[not iff] in f1. *)

(*   Definition f2 := Fn 2. *)
(*   Time Eval cbv -[not iff] in f2. *)

(*   Definition f10 := Fn 10. *)
(*   Time Eval cbv -[not iff] in f10. *)

(*   Definition f30 := Fn 30. *)
(*   Time Eval cbv -[not iff] in f30. *)
(* End FExample. *)

(* (** * Schwichtenberg formulas *) *)
(* Fixpoint ant (n : nat) := *)
(*   match n with  *)
(*     | O => True *)
(*     | S n0 => (a n -> a n -> a n0) /\ ant n0 *)
(*   end. *)
(* Definition schwicht (n : nat) : Prop := *)
(*   (a n /\ ant n) -> a 0. *)

(* Section SExample. *)
(*   Definition s1 := schwicht 1. *)
(*   Time Eval cbv -[not iff] in s1. *)

(*   Definition s2 := schwicht 2. *)
(*   Time Eval cbv -[not iff] in s2. *)

(*   Definition s10 := schwicht 10. *)
(*   Time Eval cbv -[not iff] in s10. *)

(*   Definition s30 := schwicht 30. *)
(*   Time Eval cbv -[not iff] in s30. *)
(* End SExample. *)

(* (** * Two formulas to test the sharing of subformulas *) *)
(* Definition partage := hole 3 /\ ~(hole 3). *)
(* Definition partage2 :=  *)
(*   (hole 3 <-> hole 2) \/ (hole 2 <-> hole 1) \/ (hole 1 <-> hole 3). *)
