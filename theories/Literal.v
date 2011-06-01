(** This file defines the module type of literals. *)
Require Import Sets.
Require Import SetListInstance.
Require Export Quote Ergo OrderedType SetoidList.

(** * The module type [LITERAL] *)
Module Type LITERAL.
  (** Literals must be an extension of the module type [OrderedType]
     because they will be used in finite sets and finite maps. *)
  Parameter t : Type.
  Declare Instance t_OT : OrderedType t.

  (** Special literals for true and false *)
  Parameter ltrue : t.
  Parameter lfalse : t.

  (** Literals can be negated with the function [mk_not]. There are several
     axioms that this function must verify in order to be suitable: it must
     be a morphism for literal equality [eq], it shall be involutive,
     and no literal shall be equal to its negation. *)
  Parameter mk_not : t -> t.

  Axiom mk_not_tf : (mk_not ltrue) === lfalse.
  Declare Instance mk_not_m : Proper (_eq ==> _eq) mk_not.
  Axiom mk_not_compat : forall l l', l === l' <-> (mk_not l) === (mk_not l').
  Axiom mk_not_invol : forall l, (mk_not (mk_not l)) === l.
  Axiom mk_not_fix : forall l, l === (mk_not l) -> False.

  (** Interpretation in an environment *)
  Parameter interp : varmaps -> t -> Prop.
  Axiom interp_mk_not : forall v l, ~~ (interp v l <-> ~ interp v (mk_not l)).

  (** The module also brings sets and sets of sets of literals.
     We use two different instantiation of sets of literals here, namely
     [LSet] and [Clause]. Although they are of course observationally
     equivalent, the reason we make that distinction is because they
     represent different objects and are used in different places. Having 
     different names ensures better maintenance and less confusion.

     [LSet] will be used to build partial assignments, ie. sets of literals
     that are considered to be true. [Clause], as its name suggests, will
     be used to represent clauses, ie. a disjunction of literals.
     [CSet], the module of sets of such clauses, will represent their
     conjunctions, and therefore CNF formulas.
     *)
  Notation lset := (@set t t_OT (@SetAVLInstance.SetAVL_FSet t t_OT)).
  Notation clause := (@set t t_OT (@SetListInstance.SetList_FSet t t_OT)).

  Definition clause_OT : OrderedType clause := SOT_as_OT.
  Existing Instance clause_OT.
  Notation cset := (@set clause clause_OT 
    (@SetListInstance.SetList_FSet clause clause_OT)).

  (** Expansion of proxy-literals is a distinctive feature of our 
     formalization. It allows literals to represent arbitrary formulas
     and be unfolded on the fly. Literals thus come with an [expand]
     function that returns a CNF of literals (encoded as a list of lists).
     This function shall be a morphism for literal equality.
     *)
  Parameter expand : t -> list (list t).

  Axiom expand_compat : 
    forall l l', l === l' -> eqlistA (eqlistA _eq) (expand l) (expand l').

  (** We need some sort of size in order to ensure that expansion 
     is a well-founded process, ie. that literals that arise from an
     [expand] are smaller in some sense than the original literal. 
     [size] is a morphism, is always positive and is not affected
     by negation.
     *)
  Parameter size : t -> nat.
  Declare Instance size_m : Proper (_eq ==> @eq nat) size.
  Axiom size_pos : forall l, size l > 0.
  Axiom size_mk_not : forall l, size (mk_not l) = size l.

  Fixpoint lsize (l : list t) := 
    match l with
      | nil => O
      | a::q => size a + lsize q
    end.
  Fixpoint llsize (ll : list (list t)) :=
    match ll with
      | nil => O
      | C::qq => lsize C + llsize qq
    end.
  Axiom size_expand : 
    forall l, llsize (expand l) < size l.

  (** Finally, there are properties that are not necessary for the 
     formalization and correctness proof of the decision procedure, 
     but that are required for the completeness proof. They allow 
     the completion of a partial well-formed assignment in a total model.

     In particular, it constraints some properties of proxy-literals and the 
     interaction between [expand] and [mk_not]. Again, this is not needed for
     the soundness proof.
     *)
  Parameter is_proxy : t -> bool.
  Axiom is_proxy_mk_not : forall l, is_proxy l = is_proxy (mk_not l).
  Declare Instance is_proxy_m : Proper (_eq ==> @eq bool) is_proxy.
  Axiom is_proxy_nil : forall l, is_proxy l = false -> expand l = nil.
  Axiom is_proxy_true : is_proxy ltrue = false.

  Section ExpandNot.
    Variable f : t -> Prop.

    Let fl :=
      (fix l_interp c :=
        match c with
          | nil => False
          | l::q => f l \/ l_interp q
        end).
    Let fll := 
      (fix ll_interp ll :=
        match ll with
          | nil => True
          | c::q => fl c /\ ll_interp q
        end).

    Axiom expand_mk_not : 
      forall (H_m : forall l l', l === l' -> (f l <-> f l')),
      forall l, is_proxy l = true ->  
        (forall k c, List.In c (expand l) -> List.In k c -> 
          ~~(f k <-> ~f (mk_not k))) ->
        ~~(fll (expand l) <-> ~fll (expand (mk_not l))).
  End ExpandNot.
End LITERAL.