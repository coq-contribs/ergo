Require Import Eqdep_dec Setoid Bool List Quote.
Require Export ZArith Qcanon.
Close Scope Qc_scope.
Open Scope lazy_bool_scope.

Lemma bdiscr : forall P, false = true -> P.
Proof. intros; discriminate. Qed.

(** * Different kinds of arithmetic that we handle *)
Inductive arith_domain : Set :=
| DomainNat
| DomainN
| DomainPos
| DomainZ
| DomainQ.

Definition dom_interp (d : arith_domain) : Set :=
  match d with
    | DomainNat => nat
    | DomainN => N
    | DomainPos => positive
    | DomainZ => Z
    | DomainQ => Qc
  end.
Definition dom_equal (d d' : arith_domain) : bool :=
  match d, d' with
    | DomainNat, DomainNat => true
    | DomainN, DomainN => true
    | DomainPos, DomainPos => true
    | DomainZ, DomainZ => true
    | DomainQ, DomainQ => true
    | _, _ => false
  end.

(** * Reification of types *)
Inductive type : Set :=
| typeCst (tidx : index)
| typeDefault
| typeArith (dom : arith_domain)
| typeArrow (_ _ : type).
Definition typeUnop dom :=
  typeArrow (typeArith dom) (typeArith dom).
Definition typeBinop dom :=
  typeArrow (typeArith dom) (typeArrow (typeArith dom) (typeArith dom)).

Section TInterp.
  Definition type_env := varmap Type.
  Variable vtypes : type_env.

  Inductive dummy : Set := mk_dummy.

  Fixpoint tinterp (t : type) : Type :=
    match t with
      | typeCst idx => varmap_find Set idx vtypes
      | typeDefault => dummy
      | typeArith d =>  dom_interp d
      | typeArrow t1 t2 => (tinterp t1) -> (tinterp t2)
    end.
End TInterp.

Fixpoint tequal (t t' : type) : bool :=
  match t, t' with
    | typeCst tidx, typeCst tidx' => index_eq tidx tidx'
    | typeDefault, typeDefault => true
    | typeArith dom, typeArith dom' =>  dom_equal dom dom'
    | typeArrow t1 t2, typeArrow t'1 t'2 =>
      tequal t1 t'1 &&& tequal t2 t'2
    | _, _ => false
  end.

Property tequal_1 : forall t t', tequal t t' = true -> t = t'.
Proof.
  cut (forall i i', index_eq i i' = true -> i = i').
  intro cut; induction t; destruct t'; simpl; intro; try discriminate.
  rewrite (cut _ _ H); reflexivity.
  reflexivity.
  destruct dom; destruct dom0; try discriminate H; reflexivity.
  assert (IH1 := IHt1 t'1); clear IHt1.
  assert (IH2 := IHt2 t'2); clear IHt2.
  destruct (tequal t1 t'1); simpl in H.
  rewrite IH1, IH2; auto.
  exact (bdiscr _ H).
  induction i; destruct i'; intro H; try (exact (bdiscr _ H)).
  rewrite (IHi _ H); reflexivity.
  rewrite (IHi _ H); reflexivity.
  reflexivity.
Defined.
Property tequal_2 : forall t t', t = t' -> tequal t t' = true.
Proof.
  intros t t' H; subst; induction t'; simpl.
  induction tidx; simpl; auto.
  reflexivity. destruct dom; reflexivity.
  apply andb_true_intro; auto.
Qed.
Corollary tequal_iff : forall t t', tequal t t' = true <-> t = t'.
Proof.
  intros t t'; split; intro H; [apply tequal_1 | apply tequal_2]; auto.
Qed.
Corollary type_dec : forall (t t' : type), {t = t'} + {~(t = t')}.
Proof.
  intros t t'; case_eq (tequal t t'); intro Heq; [left | right].
  apply tequal_1; auto.
  intro abs; rewrite (tequal_2 _ _ abs) in Heq; discriminate.
Qed.

(** * Terms *)
Inductive arithop : Set :=
| Plus | Minus | Opp | Mult | Div.
Inductive symbol : Set :=
| Unint (ty_idx t_idx : index) (* uninterpreted symbol *)
| Cst (dom : arith_domain) (z : dom_interp dom) (* arithmetic constant *)
| Op (dom : arith_domain) (op : arithop). (* arithmetic operations *)

Definition mk_symbol ty_idx t_idx : symbol := Unint ty_idx t_idx.

Inductive term : Set :=
| app (f : symbol) (lt : list term).
Notation terms := (list term).
Notation tnil := (@nil term).
Notation tcons := (@cons term).

Section TermInduction.
  Variable P : term -> Type.
  Variable P0 : terms -> Type.
  Variable Hlift : forall (f : symbol) (lt : terms), P0 lt -> P (app f lt).
  Variable Hnil : P0 tnil.
  Variable Hcons :
    forall (t : term), P t -> forall (lt : terms), P0 lt -> P0 (tcons t lt).

  Fixpoint term_terms_rect (t : term) : P t :=
    match t as T return P T with
      | app f l =>
        Hlift f l
        ((fix aux (l : terms) : P0 l :=
          match l as L return P0 L with
            | nil => Hnil
            | cons a q => Hcons a (term_terms_rect a) q (aux q)
          end) l)
    end.
End TermInduction.

Definition arithop_equal (o o' : arithop) : bool :=
  match o, o' with
    | Plus, Plus => true
    | Minus, Minus => true
    | Opp, Opp => true
    | Mult, Mult => true
    | Div, Div => true
    | _, _ => false
  end.
Definition cst_equal (d d' : arith_domain) :=
  match d as a, d' as b
    return dom_interp a -> dom_interp b -> bool with
    | DomainNat, DomainNat => beq_nat
    | DomainPos, DomainPos =>
      fun p p' => match Pcompare p p' Eq with Eq => true | _ => false end
    | DomainN, DomainN => Neq_bool
    | DomainZ, DomainZ => Zeq_bool
    | DomainQ, DomainQ => Qc_eq_bool
    | _, _ => fun  _ _ => false
  end.
Definition symbol_equal (f g : symbol) : bool :=
  match f, g with
    | Unint ty_idx s_idx, Unint ty_idx' s_idx' =>
      index_eq ty_idx ty_idx' &&& index_eq s_idx s_idx'
    | Cst d z, Cst d' z' => cst_equal d d' z z'
    | Op d o, Op d' o' => dom_equal d d' &&& arithop_equal o o'
    | _, _ => false
  end.
Fixpoint term_equal (u v : term) : bool :=
  match u, v with
    | app f l, app g l' =>
      if symbol_equal f g then
        (fix terms_equal l l' : bool :=
          match l, l' with
            | nil, nil => true
            | nil, _ | _, nil => false
            | t::q, t'::q' =>
              if term_equal t t' then terms_equal q q' else false
          end) l l'
        else false
  end.
Axiom term_equal_1 : forall u v, term_equal u v = true -> u = v.
Axiom term_equal_2 : forall u v, term_equal u v = false -> u <> v.

Section Interp.
  Variable vtypes : type_env.
  Notation "[| type |]" := (tinterp vtypes type).

  Definition depvarmap := {t : type & ([|t|] * varmap [|t|])%type}.
  Definition mk_depvmap (ty : type) (c : [|ty|]) (v : varmap [|ty|])
    : depvarmap := existT _ ty (c, v).
  Definition term_env := varmap depvarmap.
  Variable v : term_env.
(*   Variable qvars : varmap Z. *)

  Definition lookup_type (f : symbol) : type :=
    match f with
      | Unint ty_idx _ =>
        projT1 (varmap_find
          (existT _ typeDefault (mk_dummy, @Empty_vm dummy)) ty_idx v)
      | Cst d _ => typeArith d
      | Op d (Plus | Minus | Mult | Div) => typeBinop d
      | Op d Opp => typeUnop d
    end.
  Definition interp_op (d : arith_domain) (o : arithop)
    : [| lookup_type (Op d o) |] :=
    match d, o with
      (* nat arith : plus, mult are interpreted *)
      | DomainNat, Plus => plus
      | DomainNat, Mult => mult
      | DomainNat, Minus => fun _ _ => 0%nat
      | DomainNat, Div => fun _ _ => O%nat
      | DomainNat, Opp => fun _ => O%nat
      (* N arith : plus, mult are interpreted *)
      | DomainN, Plus => Nplus
      | DomainN, Mult => Nmult
      | DomainN, Minus => fun _ _ => N0
      | DomainN, Div => fun _ _ => N0
      | DomainN, Opp => fun _ => N0
      (* pos arith : plus, mult are interpreted *)
      | DomainPos, Plus => Pplus
      | DomainPos, Mult => Pmult
      | DomainPos, Minus => fun _ _ => xH
      | DomainPos, Div => fun _ _ => xH
      | DomainPos, Opp => fun _ => xH
      (* Z arith : plus, mult, opp, minus are interpreted *)
      | DomainZ, Plus => Zplus
      | DomainZ, Mult => Zmult
      | DomainZ, Minus => Zminus
      | DomainZ, Div => Zdiv
      | DomainZ, Opp => Zopp
      (* Q arith : plus, mult, opp, minus, div are interpreted *)
      | DomainQ, Plus => Qcplus
      | DomainQ, Mult => Qcmult
      | DomainQ, Minus => Qcminus
      | DomainQ, Div => Qcdiv
      | DomainQ, Opp => Qcopp
    end.
  Definition lookup (f : symbol) : [| lookup_type f |] :=
    match f with
      | Unint ty_idx s_idx =>
        let (d, vs) :=
          projT2 (varmap_find
            (existT _ typeDefault (mk_dummy, @Empty_vm dummy)) ty_idx v) in
          varmap_find d s_idx vs
      | Cst d q => q
(*       | Var v_idx => varmap_find 0%Z v_idx qvars *)
      | Op d op => interp_op d op
    end.

(*   Require Import Nfix. *)
(*   Nested Fixpoint type_of (t : term) : type := *)
(*     match t with *)
(*       | app f l => types_of l (lookup_type f) *)
(*     end *)
(*   with types_of (l : terms) (ret : type) : type := *)
(*     match l with *)
(*       | nil => ret *)
(*       | cons _ l => *)
(*         match ret with *)
(*           | typeArrow _ t2 => types_of l t2 *)
(*           | _ => typeDefault (* absurd *) *)
(*         end *)
(*     end. *)
  Fixpoint types_of (l : terms) (ret : type) : type :=
    match l with
      | nil => ret
      | cons _ l =>
        match ret with
          | typeArrow _ t2 => types_of l t2
          | _ => typeDefault (* dummy *)
        end
    end.
  Definition type_of (t : term) : type :=
    match t with
      | app f l => types_of l (lookup_type f)
    end.

  Inductive well_typed : term -> type -> Prop :=
  | wt_app :
    forall f lt res,
      well_typed_terms lt (lookup_type f) res ->
      well_typed (app f lt) res
  with well_typed_terms : terms -> type -> type -> Prop :=
  | wf_tnil :
    forall res, well_typed_terms tnil res res
  | wf_tcons :
    forall t lt t1 t2 res,
      well_typed_terms lt t2 res ->
      well_typed t t1 ->
      well_typed_terms (tcons t lt) (typeArrow t1 t2) res.

(*   Require Import Nfix. *)
(*   Nested Fixpoint has_type (t : term) (type : type) : bool := *)
(*     match t with *)
(*       | app f l =>  *)
(*         (fix have_type (l : terms) type res : bool := *)
(*           match l with *)
(*             | nil => tequal type res *)
(*             | cons t l =>  *)
(*               match type with *)
(*                 | typeArrow t1 t2 => has_type t t1 &&& have_type l t2 res *)
(*                 | _ => false *)
(*               end *)
(*           end           *)
(*         ) l (lookup_type f) type *)
(*     end *)
(*     with have_type (l : terms) (type res : type) : bool := *)
(*     match l with *)
(*       | nil => tequal type res *)
(*       | cons t l =>  *)
(*         match type with *)
(*           | typeArrow t1 t2 => has_type t t1 &&& have_type l t2 res *)
(*           | _ => false *)
(*         end *)
(*     end. *)

  Fixpoint has_type (t : term) (type : type) {struct t} : bool :=
    match t with
      | app f l =>
        (fix have_type (l : terms) type res : bool :=
          match l with
            | nil => tequal type res
            | cons t l =>
              match type with
                | typeArrow t1 t2 => has_type t t1 &&& have_type l t2 res
                | _ => false
              end
          end
        ) l (lookup_type f) type
    end.
  Definition have_type :=
    fix have_type (l : terms) type res : bool :=
    match l with
      | nil => tequal type res
      | cons t l =>
        match type with
          | typeArrow t1 t2 => has_type t t1 &&& have_type l t2 res
          | _ => false
        end
    end.
  Remark has_type_unfold : forall t ty,
    has_type t ty =
    match t with | app f l => have_type l (lookup_type f) ty end.
  Proof.
    intros; unfold has_type; destruct t; reflexivity.
  Qed.

  Property has_type_1 : forall t ty, has_type t ty = true -> well_typed t ty.
  Proof.
    intro t; pattern t; apply term_terms_rect
      with (P0 := fun lt => forall ty res,
        have_type lt ty res = true -> well_typed_terms lt ty res); clear t.
    intros f lt IH ty Happ; simpl in Happ; constructor; auto.
    intros ty res H; simpl in H; rewrite tequal_iff in H; subst; constructor.
    intros t IHt lt IHlt ty res H; simpl in H.
    destruct ty; try discriminate; constructor;
      destruct (andb_prop _ _ H); auto.
  Qed.
  Property has_type_2 : forall t ty, well_typed t ty -> has_type t ty = true.
  Proof.
    intro t; pattern t; apply term_terms_rect
      with (P0 := fun lt => forall ty res,
        well_typed_terms lt ty res -> have_type lt ty res = true); clear t.
    intros f lt IH ty Happ; inversion Happ; subst; simpl; auto.
    intros ty res H; inversion H; subst; simpl; apply tequal_2; auto.
    intros t IHt lt IHlt ty res H; inversion H; subst.
    simpl; apply andb_true_intro; auto.
  Qed.
  Corollary has_type_iff :
    forall t ty, has_type t ty = true <-> well_typed t ty.
  Proof.
    intros t t'; split; intro H; [apply has_type_1 | apply has_type_2]; auto.
  Qed.
  Corollary well_typed_dec :
    forall t ty, { well_typed t ty } + {~(well_typed t ty)}.
  Proof.
    intros; case_eq (has_type t ty); intro H; [left | right].
    apply has_type_1; auto.
    intro c; rewrite (has_type_2 _ _ c) in H; discriminate.
  Qed.

(*   Require Import Nfix. *)
(*   Nested Fixpoint interp (t : term) (ty : type) (H : has_type t ty = true) *)
(*     : [| ty |] := *)
(*     (match t as a *)
(*        return has_type a ty = true -> [| ty |] with *)
(*        | app f l => *)
(*          fun H => interps l _ ty (lookup f) H *)
(*      end) H *)
(*   with interps (l : terms) (ty res : type) (f : [| ty |]) *)
(*       (H : have_type l ty res = true) : [| res |] := *)
(*       (match l as a return have_type a ty res = true -> [| res |] with *)
(*          | nil => *)
(*            fun H => eq_rect _ (fun x => [| x |]) f _ (tequal_1 _ _ H) *)
(*          | cons t lt => *)
(*            (match ty as b *)
(*               return [| b |] -> have_type (tcons t lt) b res = true *)
(*               -> [| res |] with *)
(*               | typeArrow t1 t2 => *)
(*                 fun f H => *)
(*                   let H1 := proj1 (andb_prop _ _ H) in *)
(*                   let H2 := proj2 (andb_prop _ _ H) in *)
(*                   interps_ lt t2 res (f (interp t t1 H1)) H2 *)
(*               | _ => *)
(*                 fun f => bdiscr [| res |] *)
(*             end) f *)
(*        end) H. *)

  Section Interps.
    Variable interp :
      forall (t : term) (ty : type) (H : has_type t ty = true), [| ty |].
    Fixpoint interps_ (l : terms) (ty res : type) (f : [| ty |])
      (H : have_type l ty res = true) : [| res |] :=
      (match l as a return have_type a ty res = true -> [| res |] with
         | nil =>
           fun H => eq_rect _ (fun x => [| x |]) f _ (tequal_1 _ _ H)
         | cons t lt =>
           (match ty as b
              return [| b |] -> have_type (tcons t lt) b res = true
              -> [| res |] with
              | typeArrow t1 t2 =>
                fun f H =>
                  let H1 := proj1 (andb_prop _ _ H) in
                  let H2 := proj2 (andb_prop _ _ H) in
                  interps_ lt t2 res (f (interp t t1 H1)) H2
              | _ =>
                fun f => bdiscr [| res |]
            end) f
       end) H.
  End Interps.
  Fixpoint interp (t : term) (ty : type) (H : has_type t ty = true)
    : [| ty |] :=
    (match t as a
       return has_type a ty = true -> [| ty |] with
       | app f l =>
         fun H => interps_ interp l _ ty (lookup f) H
     end) H.
  Definition interps := interps_ interp.
  Remark interp_unfold : forall t ty H, interp t ty H =
    (match t as a return has_type a ty = true -> [| ty |] with
       | app f l =>
         fun H => interps l _ ty (lookup f) H
     end) H.
  Proof. intros; unfold interp; destruct t; reflexivity. Qed.

  Definition interp' (t : term) := interp t (type_of t).
End Interp.

Module Test.
  Close Scope Z_scope.
  Implicit Arguments Empty_vm [[A]].

  Definition nat_idx := End_idx.
  Definition bool_idx := Left_idx End_idx.
  Definition nat_arrow_bool_idx := Right_idx End_idx.
  Definition nat_arrow_nat_idx := Right_idx (Left_idx End_idx).

  Definition vtypes : type_env :=
    @Node_vm Type nat
      (@Node_vm Type bool Empty_vm Empty_vm)
      Empty_vm.
  Notation "[| type |]" := (tinterp vtypes type).

  Definition tnat : type := typeCst nat_idx.
  Definition tbool : type := typeCst bool_idx.
  Definition tnat_arrow_bool : type := typeArrow tnat tbool.
  Definition tnat_arrow_nat : type := typeArrow tnat tnat.

  Variable natx : nat.
  Variable boolx : bool.

  Definition nat_varmap : varmap nat :=
    Node_vm 0%nat
    (Node_vm 1%nat (Node_vm natx Empty_vm Empty_vm) Empty_vm)
    (Node_vm 2 Empty_vm Empty_vm).

  (** Paths to reified values *)
  Definition n0 := Unint nat_idx End_idx.
  Definition n1 := Unint nat_idx (Left_idx End_idx).
  Definition n2 := Unint nat_idx (Right_idx End_idx).
  Definition nx := Unint nat_idx (Left_idx (Left_idx End_idx)).

  Definition bool_varmap : varmap bool :=
    Node_vm true
    (Node_vm false Empty_vm Empty_vm)
    (Node_vm boolx (Node_vm false Empty_vm Empty_vm) Empty_vm).

  (** Path to reified values *)
  Definition btrue := Unint bool_idx End_idx.
  Definition bfalse := Unint bool_idx (Left_idx End_idx).
  Definition bx := Unint bool_idx (Right_idx End_idx).
  Definition bfalse2 := Unint bool_idx (Left_idx (Left_idx End_idx)).

  Variable natbool : nat -> bool.
  Definition nat_arrow_bool_varmap : varmap (nat -> bool) :=
    Node_vm (fun x : nat => match x with 0 => true | _ => false end)
    (Node_vm natbool Empty_vm Empty_vm)
    Empty_vm.

  Variable natnat : nat -> nat.
  Definition nat_arrow_nat_varmap : varmap (nat -> nat) :=
    Node_vm S (Node_vm natnat Empty_vm Empty_vm) Empty_vm.

  (** Path to reified values *)
  Definition test0 := Unint nat_arrow_bool_idx End_idx.
  Definition anatbool := Unint nat_arrow_bool_idx (Left_idx End_idx).
  Definition succ := Unint nat_arrow_nat_idx End_idx.
  Definition anatnat := Unint nat_arrow_nat_idx (Left_idx End_idx).

  Definition variables : term_env vtypes :=
    Node_vm (existT _ tnat (0%nat, nat_varmap))
    (Node_vm (existT _ tbool (false, bool_varmap)) Empty_vm Empty_vm)
    (Node_vm (existT _ tnat_arrow_bool (fun x => false, nat_arrow_bool_varmap))
      (Node_vm (existT _ tnat_arrow_nat (fun x => O, nat_arrow_nat_varmap))
        Empty_vm Empty_vm)
      Empty_vm).
(*   Definition qvars : varmap Z := Empty_vm. *)

  Definition interp (t : term) := interp' vtypes variables t.

  Definition two := app n2 tnil.
  Definition itwo : nat := interp two (refl_equal _).
  Time Eval vm_compute in itwo.
  Definition zero := app n0 tnil.
  Definition izero : nat := interp zero (refl_equal _).
  Time Eval vm_compute in izero.
  Definition x := app nx tnil.
  Definition ix : nat := interp x (refl_equal _).
  Time Eval vm_compute in ix.

  Definition a := app test0 (tcons zero tnil).
  Definition ia : bool := interp a (refl_equal _).
  Time Eval vm_compute in ia.

  Definition b := app test0 (tcons two tnil).
  Definition ib : bool := interp b (refl_equal _).
  Time Eval vm_compute in ib.

  Definition anatbool_x := app anatbool (tcons x tnil).
  Definition inbx : bool := interp anatbool_x (refl_equal _).
  Time Eval vm_compute in inbx.

  Fixpoint power f a (n : nat) :=
    match n with
      | O => a
      | S n0 => app f (tcons (power f a n0) tnil)
    end.
  Definition fx := power anatnat x 1.
  Definition f3x := power anatnat x 3.
  Definition f5x := power anatnat x 5.
  Time Eval vm_compute in (interp f5x (refl_equal _)).
End Test.

Module TestWithNat.
  Open Scope nat_scope.
  Implicit Arguments Empty_vm [[A]].
  Definition nat_idx := End_idx.
  Definition bool_idx := Left_idx End_idx.
  Definition nat_arrow_bool_idx := Right_idx End_idx.
  Definition nat_arrow_nat_idx := Right_idx (Left_idx End_idx).

  Definition vtypes : type_env :=
    @Node_vm Type nat
      (@Node_vm Type bool Empty_vm Empty_vm)
      Empty_vm.
  Notation "[| type |]" := (tinterp vtypes type).

  Definition tnat : type := typeArith DomainNat.
  Definition tbool : type := typeCst bool_idx.
  Definition tnat_arrow_bool : type := typeArrow tnat tbool.
  Definition tnat_arrow_nat : type := typeArrow tnat tnat.

  Variable natx : nat.
  Variable boolx : bool.

  Definition nat_varmap : varmap nat :=
    Node_vm natx Empty_vm Empty_vm.

  (** Paths to reified values *)
  Definition n0 := Cst DomainNat 0.
  Definition n1 := Cst DomainNat 1.
  Definition n2 := Cst DomainNat 2.
  Definition nx := Unint nat_idx End_idx.

  Definition bool_varmap : varmap bool :=
    Node_vm true
    (Node_vm false Empty_vm Empty_vm)
    (Node_vm boolx (Node_vm false Empty_vm Empty_vm) Empty_vm).

  (** Path to reified values *)
  Definition btrue := Unint bool_idx End_idx.
  Definition bfalse := Unint bool_idx (Left_idx End_idx).
  Definition bx := Unint bool_idx (Right_idx End_idx).
  Definition bfalse2 := Unint bool_idx (Left_idx (Left_idx End_idx)).

  Variable natbool : nat -> bool.
  Definition nat_arrow_bool_varmap : varmap (nat -> bool) :=
    Node_vm (fun x : nat => match x with 0 => true | _ => false end)
    (Node_vm natbool Empty_vm Empty_vm)
    Empty_vm.

  Variable natnat : nat -> nat.
  Definition nat_arrow_nat_varmap : varmap (nat -> nat) :=
    Node_vm S (Node_vm natnat Empty_vm Empty_vm) Empty_vm.

  (** Path to reified values *)
  Definition test0 := Unint nat_arrow_bool_idx End_idx.
  Definition anatbool := Unint nat_arrow_bool_idx (Left_idx End_idx).
  Definition succ := Unint nat_arrow_nat_idx End_idx.
  Definition anatnat := Unint nat_arrow_nat_idx (Left_idx End_idx).

  Definition variables : term_env vtypes :=
    Node_vm (existT _ tnat (0, nat_varmap))
    (Node_vm (existT _ tbool (false, bool_varmap)) Empty_vm Empty_vm)
    (Node_vm (existT _ tnat_arrow_bool (fun x => false, nat_arrow_bool_varmap))
      (Node_vm (existT _ tnat_arrow_nat (fun x => O, nat_arrow_nat_varmap))
        Empty_vm Empty_vm)
      Empty_vm).

  Definition interp (t : term) := interp' vtypes variables t.

  Definition two := app n2 tnil.
  Definition itwo : nat := interp two (refl_equal _).
  Time Eval vm_compute in itwo.
  Definition zero := app n0 tnil.
  Definition izero : nat := interp zero (refl_equal _).
  Time Eval vm_compute in izero.
  Definition x := app nx tnil.
  Definition ix : nat := interp x (refl_equal _).
  Time Eval vm_compute in ix.

  Definition a := app test0 (tcons zero tnil).
  Definition ia : bool := interp a (refl_equal _).
  Time Eval vm_compute in ia.

  Definition b := app test0 (tcons two tnil).
  Definition ib : bool := interp b (refl_equal _).
  Time Eval vm_compute in ib.

  Definition anatbool_x := app anatbool (tcons x tnil).
  Definition inbx : bool := interp anatbool_x (refl_equal _).
  Time Eval vm_compute in inbx.

  Fixpoint power f a (n : nat) :=
    match n with
      | O => a
      | S n0 => app f (tcons (power f a n0) tnil)
    end.
  Definition fx := power anatnat x 1.
  Definition f3x := power anatnat x 3.
  Definition f5x := power anatnat x 5.
  Time Eval vm_compute in (interp f5x (refl_equal _)).
End TestWithNat.

Module BoolasDT <: DecidableType.
  Definition U := bool.
  Definition eq_dec := bool_dec.
End BoolasDT.
Module BoolEqDep := DecidableEqDep(BoolasDT).

Module TypeasDT <: DecidableType.
  Definition U := type.
  Definition eq_dec := type_dec.
End TypeasDT.
Module TypeEqDep := DecidableEqDep(TypeasDT).

Section CanonicalStructure.
  Variable vtypes : varmap Type.
  Variable v : varmap (depvarmap vtypes).

  Definition dom := option (sigT (tinterp vtypes)).
  Definition int (t : term) : dom :=
    let ty := type_of vtypes v t in
      (match has_type vtypes v t ty as a
         return has_type vtypes v t ty = a -> dom with
         | true => fun H =>
           Some (existT (tinterp vtypes) ty (interp' vtypes v t H))
         | false => fun _ => None
       end) (refl_equal _).
  Definition eq (t t' : term) := int t = int t'.

  Property eq_refl : forall t, eq t t.
  Proof. reflexivity. Qed.
  Property eq_sym : forall t t', eq t t' -> eq t' t.
  Proof. congruence. Qed.
  Property eq_trans : forall t t' t'', eq t t' -> eq t' t'' -> eq t t''.
  Proof. congruence. Qed.

  Lemma has_type_is_type_of :
    forall t ty, has_type vtypes v t ty = true -> ty = type_of vtypes v t.
  Proof.
    intro t; pattern t.
    apply term_terms_rect with
      (P0 := fun lt => forall ty res, have_type vtypes v lt ty res = true ->
        res = types_of lt ty); clear t.
    intros f lt IH ty Heq; rewrite (IH _ _ Heq); reflexivity.
    intros ty res H; simpl in *; symmetry; apply tequal_1; auto.
    intros t IHt lt IHlt ty res Heq.
    simpl in Heq; destruct ty; try discriminate.
    destruct (andb_prop _ _ Heq) as [H1 H2]; simpl.
    apply IHlt; auto.
  Qed.

  Inductive eq_terms : terms -> terms -> Prop :=
  | eq_terms_nil : eq_terms nil nil
  | eq_terms_cons :
    forall a a' q q', eq a a' -> eq_terms q q' -> eq_terms (a::q) (a'::q').

  Property eq_terms_refl : forall l, eq_terms l l.
  Proof. induction l; constructor (auto using eq_refl). Qed.
  Property eq_terms_sym : forall l l', eq_terms l l' -> eq_terms l' l.
  Proof.
    intros l l' H; induction H; subst; constructor (auto using eq_sym).
  Qed.
  Property eq_terms_trans : forall l l' l'',
    eq_terms l l' -> eq_terms l' l'' -> eq_terms l l''.
  Proof.
    intros l l' l'' H; revert l''; induction H; intros l'' H'; inversion H';
      subst; constructor; eauto using eq_trans.
  Qed.

  Lemma types_of_congr :
    forall ty lt lt', eq_terms lt lt' -> types_of lt ty = types_of lt' ty.
  Proof.
    intros ty lt lt' Heq; revert ty; induction Heq; intro ty; simpl.
    reflexivity.
    destruct ty; auto.
  Qed.
  Lemma type_of_congr :
    forall f lt lt', eq_terms lt lt' ->
      type_of vtypes v (app f lt) = type_of vtypes v (app f lt').
  Proof.
    intros; unfold type_of; rewrite (types_of_congr _ lt lt' H); auto.
  Qed.

  Lemma has_type_congr :
    forall ty t t', eq t t' ->
      has_type vtypes v t ty = has_type vtypes v t' ty.
  Proof.
    intros ty t t' Heq.
    case_eq (has_type vtypes v t ty); intro H;
      case_eq (has_type vtypes v t' ty); intro H'; auto.
    assert (R := has_type_is_type_of t ty H); subst.
    unfold eq, int in Heq.
    set (Z := interp' vtypes v t) in *; clearbody Z.
    destruct (has_type vtypes v t (type_of vtypes v t)); try discriminate.
    set (Z' := interp' vtypes v t') in *; clearbody Z'.
    case_eq (has_type vtypes v t' (type_of vtypes v t')); intro H''.
    cut (type_of vtypes v t = type_of vtypes v t' -> False);
      [ intro cut |
        intro abs; rewrite abs in H'; rewrite H' in H''; discriminate].
    destruct (has_type vtypes v t' (type_of vtypes v t')); try discriminate.
    inversion Heq; contradiction cut; assumption.
    destruct (has_type vtypes v t' (type_of vtypes v t')); try discriminate.
    assert (R := has_type_is_type_of t' ty H'); subst.
    unfold eq, int in Heq.
    set (Z' := interp' vtypes v t') in *; clearbody Z'.
    destruct (has_type vtypes v t' (type_of vtypes v t')); try discriminate.
    set (Z := interp' vtypes v t) in *; clearbody Z.
    case_eq (has_type vtypes v t (type_of vtypes v t)); intro H''.
    cut (type_of vtypes v t = type_of vtypes v t' -> False);
      [ intro cut |
        intro abs; rewrite abs in H''; rewrite H in H''; discriminate].
    destruct (has_type vtypes v t (type_of vtypes v t)); try discriminate.
    inversion Heq; contradiction cut; assumption.
    destruct (has_type vtypes v t (type_of vtypes v t)); try discriminate.
  Qed.
  Lemma have_type_congr :
    forall lt ty res lt', eq_terms lt lt' ->
      have_type vtypes v lt ty res = have_type vtypes v lt' ty res.
  Proof.
    induction lt; intros ty res lt' Heq; inversion Heq; subst.
    reflexivity.
    simpl; destruct ty; auto.
    rewrite (IHlt _ _ _ H3), (has_type_congr _ _ _ H1); reflexivity.
  Qed.

  Corollary has_type_type_of_congr :
    forall f lt lt', eq_terms lt lt' ->
      has_type vtypes v (app f lt) (type_of vtypes v (app f lt)) =
      has_type vtypes v (app f lt') (type_of vtypes v (app f lt')).
  Proof.
    intros f lt lt' Heq.
    rewrite (type_of_congr f lt lt' Heq).
    generalize (type_of vtypes v (app f lt')) as ty.
    intro ty; rewrite 2has_type_unfold; revert ty.
    induction Heq; intro ty; simpl.
    reflexivity.
    unfold has_type in *; destruct (lookup_type vtypes v f); auto.
    fold (has_type vtypes v a t1); fold (has_type vtypes v a' t1).
    fold (have_type vtypes v q t2); fold (have_type vtypes v q' t2).
    rewrite (has_type_congr t1 a a' H).
    rewrite (have_type_congr _ _ _ _ Heq); reflexivity.
  Qed.

  Lemma interp_congr : forall ty f lt lt' H H',
    eq_terms lt lt' ->
    interp vtypes v (app f lt) ty H = interp vtypes v (app f lt') ty H'.
  Proof.
    intros ty f lt lt' H H' Heq.
    change (interps vtypes v lt _ ty (lookup vtypes v f) H =
      interps vtypes v lt' _ ty (lookup vtypes v f) H').
    generalize (lookup vtypes v f) as F.
    change (have_type vtypes v lt' (lookup_type vtypes v f) ty = true) in H'.
    change (have_type vtypes v lt (lookup_type vtypes v f) ty = true) in H.
    revert H H'; remember (lookup_type vtypes v f) as tyf; clear Heqtyf.
    revert ty tyf; induction Heq; intros res tyf Hty Hty' fi.
    simpl in *; assert (R := tequal_1 _ _ Hty); subst.
    do 2 rewrite <- (Eqdep_dec.eq_rect_eq_dec type_dec); reflexivity.
    unfold interps; destruct tyf.
    rewrite (BoolEqDep.UIP false true Hty Hty'); reflexivity.
    rewrite (BoolEqDep.UIP false true Hty Hty'); reflexivity.
    rewrite (BoolEqDep.UIP false true Hty Hty'); reflexivity.
    change (
      (let h1 := has_type vtypes v a tyf1 in
       let h2 := have_type vtypes v q tyf2 res in
       let H1 := proj1 (andb_prop h1 h2 Hty) in
       let H2 := proj2 (andb_prop h1 h2 Hty) in
         interps vtypes v q tyf2 res (fi (interp vtypes v a tyf1 H1)) H2) =
      (let h1 := has_type vtypes v a' tyf1 in
       let h2 := have_type vtypes v q' tyf2 res in
       let H1 := proj1 (andb_prop h1 h2 Hty') in
       let H2 := proj2 (andb_prop h1 h2 Hty') in
         interps vtypes v q' tyf2 res (fi (interp vtypes v a' tyf1 H1)) H2)).
    set (h1 := has_type vtypes v a tyf1).
    set (h2 := have_type vtypes v q tyf2 res).
    set (H1 := proj1 (andb_prop h1 h2 Hty)).
    set (h1' := has_type vtypes v a' tyf1).
    set (h2' := have_type vtypes v q' tyf2 res).
    set (H1' := proj1 (andb_prop h1' h2' Hty')).
    simpl.

    cut (fi (interp vtypes v a tyf1 H1) = fi (interp vtypes v a' tyf1 H1')).
    intro R; fold H1; rewrite R; apply IHHeq.
    clear IHHeq; f_equal; unfold eq, int, interp' in H.
    assert (Rty := has_type_is_type_of _ _ H1).
    assert (Rty' := has_type_is_type_of _ _ H1').
    clearbody H1 H1'; clear Hty Hty'.
    unfold h1, h2, h1', h2' in *; clear h1 h2 h1' h2'; subst.
    revert H fi H1 H1' Rty'.
    generalize (type_of vtypes v a) as ty;
      generalize (type_of vtypes v a') as ty'; intros; subst.
    set (Z := interp vtypes v a ty') in *; clearbody Z.
    set (Z' := interp vtypes v a' ty') in *; clearbody Z'.
    destruct (has_type vtypes v a ty'); try discriminate.
    destruct (has_type vtypes v a' ty'); try discriminate.
    inversion H; subst.
    rewrite (BoolEqDep.UIP _ _ H1 H1'), (BoolEqDep.UIP_refl _ H1').
    exact (TypeEqDep.inj_pairT2 _ _ _ _ H2).
  Qed.

  Property eq_congr : forall f l l',
    eq_terms l l' -> eq (app f l) (app f l').
  Proof.
    intros f l l' Heq.
    unfold eq, int.
    assert (Teq := has_type_type_of_congr f l l' Heq).
    assert (icongr := fun H H' =>
      interp_congr (type_of vtypes v (app f l)) f l l' H H' Heq).
    assert (R :=  type_of_congr f l l' Heq).
    unfold interp'.
    revert Teq R icongr.
    generalize (type_of vtypes v (app f l)) as ty;
      generalize (type_of vtypes v (app f l')) as ty'.
    intros ty ? ? Teq icongr; subst.
    set (Z := interp vtypes v (app f l) ty) in *; clearbody Z.
    set (Z' := interp vtypes v (app f l') ty) in *; clearbody Z'.
    destruct (has_type vtypes v (app f l) ty);
      destruct (has_type vtypes v (app f l') ty);
        try discriminate; auto.
    rewrite (icongr (refl_equal _) (refl_equal _)); reflexivity.
  Qed.
End CanonicalStructure.
(* Print Assumptions model. *)

Theorem replace : forall vty vsy ty ra rb a b,
  int vty vsy a = Some (existT _ ty ra) ->
  int vty vsy b = Some (existT _ ty rb) ->
    (ra = rb <-> eq vty vsy a b).
Proof.
  intros vty vsy ty ra rb a b Ha Hb;
    unfold eq; split; intro R.
  congruence.
  rewrite Ha, Hb in R; inversion R.
  exact (TypeEqDep.inj_pairT2 _ _ _ _ H0).
Qed.

Lemma has_type_irrelevant :
  forall vty vsy r ty (H H' : has_type vty vsy r ty = true), H = H'.
Proof.
  intros; apply BoolEqDep.UIP.
Qed.
Lemma interp_irrelevant :
  forall vty vsy r ty (H H' : has_type vty vsy r ty = true),
    interp vty vsy r ty H = interp vty vsy r ty H'.
Proof.
  intros; rewrite (has_type_irrelevant vty vsy r ty H H'); reflexivity.
Qed.

Theorem replace' :
  forall vty vsy (ra rb : term) (ty : type)
    (Ha : has_type vty vsy ra ty = true) (Hb : has_type vty vsy rb ty = true),
    interp vty vsy ra ty Ha = interp vty vsy rb ty Hb
    <-> eq vty vsy ra rb.
Proof.
  intros.
  unfold eq, int, interp'.
  assert (ty = type_of vty vsy ra).
  apply has_type_is_type_of; assumption.
  rewrite <- H; clear H.
  assert (ty = type_of vty vsy rb).
  apply has_type_is_type_of; assumption.
  rewrite <- H; clear H.
  assert (Iirr := fun r => interp_irrelevant vty vsy r ty).
  assert (Iirra := Iirr ra Ha). assert (Iirrb := Iirr rb Hb). clear Iirr.
  set (Ia := interp vty vsy ra ty) in *; clearbody Ia.
  set (Ib := interp vty vsy rb ty) in *; clearbody Ib.
  set (Za := has_type vty vsy ra ty) in *; clearbody Za.
  set (Zb := has_type vty vsy rb ty) in *; clearbody Zb.
  destruct Za; destruct Zb; try discriminate.
  generalize (Iirra (refl_equal _)) (Iirrb (refl_equal _)); intros; split.
  intro; congruence.
  intro abs; inversion abs;
    assert (ZZ := TypeEqDep.inj_pairT2 _ _ _ _ H2); congruence.
Qed.

(* Section CanonicalStructure2. *)
(*   Variable vtypes : varmap Type. *)
(*   Variable v : varmap (depvarmap vtypes). *)

(*   Inductive int_spec (t : term) : dom vtypes -> Prop := *)
(*   | int_spec_Some :  *)
(*     let ty := type_of vtypes v t in *)
(*       forall (it : tinterp vtypes ty) *)
(*         (H_wt : has_type vtypes v t ty = true) *)
(*         (Hit : it = interp vtypes v t ty H_wt), *)
(*         int_spec t (Some (existT _ ty it)) *)
(*   | int_spec_None :  *)
(*     forall (H_nwt : has_type vtypes v t (type_of vtypes v t) = false), *)
(*       int_spec t None. *)
(*   Theorem int_dec : forall t, int_spec t (int vtypes v t). *)
(*   Proof. *)
(*     intro t; unfold int, interp'. *)
(*     assert (C1 := int_spec_Some t); revert C1; simpl. *)
(*     set (Z := interp vtypes v t (type_of vtypes v t)); clearbody Z; revert Z. *)
(*     destruct (has_type vtypes v t (type_of vtypes v t)) as [ ]_eqn:Hht. *)
(*     intros; apply C1 with (refl_equal _); auto. *)
(*     intros; constructor auto. *)
(*   Qed. *)
(*   Tactic Notation "decide" "int" := *)
(*     match goal with *)
(*       | |- context f [int vtypes v ?T] => destruct (int_dec T) *)
(*       | _ => fail "No occurrence of 'int' found in goal." *)
(*     end.     *)

(*   Require Import Nfix. *)
(*   Nested Fixpoint eq2 (x y : term) : Prop := *)
(*     match int vtypes v x, int vtypes v y with *)
(*       | Some sx, Some sy => sx = sy *)
(*       | Some _, None | None, Some _ => False *)
(*       | None, None =>  *)
(*         match x, y with *)
(*           | app f l, app g l' => f = g /\ eq2_terms l l' *)
(*         end *)
(*     end *)
(*   with eq2_terms (lx ly : terms) : Prop := *)
(*     match lx, ly with *)
(*       | nil, nil => True *)
(*       | cons _ _, nil | nil, cons _ _ => False *)
(*       | x::qx, y::qy => eq2 x y /\ eq2_terms qx qy *)
(*     end. *)


(*   Property eq2_refl : forall t, eq2 t t. *)
(*   Proof.  *)
(*     intro t; unfold eq2. *)
(*     decide int; reflexivity. *)
(*   Qed. *)
(*   Property eq2_sym : forall t t', eq2 t t' -> eq2 t' t. *)
(*   Proof. *)
(*     intros t t'; unfold eq2. *)
(*     do 2 decide int; intuition. *)
(*   Qed. *)
(*   Property eq2_trans : forall t t' t'', eq2 t t' -> eq2 t' t'' -> eq2 t t''. *)
(*   Proof.  *)
(*     intros t t' t''; unfold eq2. *)
(*     do 3 decide int; intuition; eapply transitivity; eassumption. *)
(*   Qed. *)

(*   Inductive eq2_terms : terms -> terms -> Prop := *)
(*   | eq2_terms_nil : eq2_terms nil nil *)
(*   | eq2_terms_cons :  *)
(*     forall a a' q q', eq2 a a' -> eq2_terms q q' -> eq2_terms (a::q) (a'::q'). *)
(*   Property eq2_terms_refl : forall l, eq2_terms l l. *)
(*   Proof. induction l; constructor (auto using eq2_refl). Qed. *)
(*   Property eq2_terms_sym : forall l l', eq2_terms l l' -> eq2_terms l' l. *)
(*   Proof. *)
(*     intros l l' H; induction H; subst; constructor (auto using eq2_sym). *)
(*   Qed. *)
(*   Property eq2_terms_trans : forall l l' l'',  *)
(*     eq2_terms l l' -> eq2_terms l' l'' -> eq2_terms l l''. *)
(*   Proof. *)
(*     intros l l' l'' H; revert l''; induction H; intros l'' H'; inversion H';  *)
(*       subst; constructor; eauto using eq2_trans. *)
(*   Qed. *)

(*   Lemma types_of_congr2 : *)
(*     forall ty lt lt', eq2_terms lt lt' -> types_of lt ty = types_of lt' ty. *)
(*   Proof. *)
(*     intros ty lt lt' Heq; revert ty; induction Heq; intro ty; simpl. *)
(*     reflexivity. *)
(*     destruct ty; auto. *)
(*   Qed. *)
(*   Lemma type_of_congr2 : *)
(*     forall f lt lt', eq2_terms lt lt' -> *)
(*       type_of vtypes v (app f lt) = type_of vtypes v (app f lt'). *)
(*   Proof. *)
(*     intros; unfold type_of; rewrite (types_of_congr2 _ lt lt' H); auto. *)
(*   Qed. *)

(*   Lemma has_type_congr2 : *)
(*     forall ty t t', eq2 t t' -> *)
(*       has_type vtypes v t ty = has_type vtypes v t' ty. *)
(*   Proof. *)
(*     intros ty t t'; unfold eq2. *)
(*     do 2 decide int; intuition. *)
(*     inversion H; subst; clear H H2. *)
(*     case_eq (has_type vtypes v t ty); intro. *)
(*     rewrite (has_type_is_type_of _ _ _ _ H) in *; congruence. *)
(*     case_eq (has_type vtypes v t' ty); intro; auto. *)
(*     rewrite (has_type_is_type_of _ _ _ _ H0) in *. *)
(*     fold ty1 in H; congruence. *)
(*     congruence. *)
(*   Qed. *)
(*   Lemma have_type_congr2 : *)
(*     forall lt ty res lt', eq2_terms lt lt' -> *)
(*       have_type vtypes v lt ty res = have_type vtypes v lt' ty res. *)
(*   Proof. *)
(*     induction lt; intros ty res lt' Heq; inversion Heq; subst. *)
(*     reflexivity. *)
(*     simpl; destruct ty; auto. *)
(*     rewrite (IHlt _ _ _ H3), (has_type_congr2 _ _ _ H1); reflexivity. *)
(*   Qed. *)

(*   Corollary has_type_type_of_congr2 : *)
(*     forall f lt lt', eq2_terms lt lt' -> *)
(*       has_type vtypes v (app f lt) (type_of vtypes v (app f lt)) = *)
(*       has_type vtypes v (app f lt') (type_of vtypes v (app f lt')). *)
(*   Proof. *)
(*     intros f lt lt' Heq. *)
(*     rewrite (type_of_congr2 f lt lt' Heq). *)
(*     generalize (type_of vtypes v (app f lt')) as ty. *)
(*     intro ty; rewrite 2has_type_unfold; revert ty. *)
(*     induction Heq; intro ty; simpl. *)
(*     reflexivity. *)
(*     unfold has_type in *; destruct (lookup_type vtypes v f); auto. *)
(*     fold (has_type vtypes v a t1); fold (has_type vtypes v a' t1). *)
(*     fold (have_type vtypes v q t2); fold (have_type vtypes v q' t2). *)
(*     rewrite (has_type_congr2 t1 a a' H). *)
(*     rewrite (have_type_congr2 _ _ _ _ Heq); reflexivity. *)
(*   Qed. *)

(*   Lemma interp_congr2 : forall ty f lt lt' H H', *)
(*     eq2_terms lt lt' -> *)
(*     interp vtypes v (app f lt) ty H = interp vtypes v (app f lt') ty H'. *)
(*   Proof. *)
(*     intros ty f lt lt' H H' Heq. *)
(*     change (interps vtypes v lt _ ty (lookup vtypes v f) H = *)
(*       interps vtypes v lt' _ ty (lookup vtypes v f) H'). *)
(*     generalize (lookup vtypes v f) as F. *)
(*     change (have_type vtypes v lt' (lookup_type vtypes v f) ty = true) in H'. *)
(*     change (have_type vtypes v lt (lookup_type vtypes v f) ty = true) in H. *)
(*     revert H H'; remember (lookup_type vtypes v f) as tyf; clear Heqtyf. *)
(*     revert ty tyf; induction Heq; intros res tyf Hty Hty' fi. *)
(*     simpl in *; assert (R := tequal_1 _ _ Hty); subst. *)
(*     do 2 rewrite <- (Eqdep_dec.eq_rect_eq_dec type_dec); reflexivity. *)
(*     unfold interps; destruct tyf. *)
(*     rewrite (BoolEqDep.UIP false true Hty Hty'); reflexivity. *)
(*     rewrite (BoolEqDep.UIP false true Hty Hty'); reflexivity. *)
(*     rewrite (BoolEqDep.UIP false true Hty Hty'); reflexivity. *)
(*     change ( *)
(*       (let h1 := has_type vtypes v a tyf1 in *)
(*        let h2 := have_type vtypes v q tyf2 res in *)
(*        let H1 := proj1 (andb_prop h1 h2 Hty) in *)
(*        let H2 := proj2 (andb_prop h1 h2 Hty) in *)
(*          interps vtypes v q tyf2 res (fi (interp vtypes v a tyf1 H1)) H2) = *)
(*       (let h1 := has_type vtypes v a' tyf1 in *)
(*        let h2 := have_type vtypes v q' tyf2 res in *)
(*        let H1 := proj1 (andb_prop h1 h2 Hty') in *)
(*        let H2 := proj2 (andb_prop h1 h2 Hty') in *)
(*          interps vtypes v q' tyf2 res (fi (interp vtypes v a' tyf1 H1)) H2)). *)
(*     set (h1 := has_type vtypes v a tyf1). *)
(*     set (h2 := have_type vtypes v q tyf2 res). *)
(*     set (H1 := proj1 (andb_prop h1 h2 Hty)). *)
(*     set (h1' := has_type vtypes v a' tyf1). *)
(*     set (h2' := have_type vtypes v q' tyf2 res). *)
(*     set (H1' := proj1 (andb_prop h1' h2' Hty')). *)
(*     simpl. *)

(*     cut (fi (interp vtypes v a tyf1 H1) = fi (interp vtypes v a' tyf1 H1')). *)
(*     intro R; fold H1; rewrite R; apply IHHeq. *)
(*     clear IHHeq; f_equal; unfold eq2 in H. *)
(*     revert H; do 2 decide int; intro H; try contradiction. *)
(*     assert (Rty := has_type_is_type_of _ _ _ _ H1). *)
(*     assert (Rty' := has_type_is_type_of _ _ _ _ H1'). *)
(*     clearbody H1 H1'; clear Hty Hty'. *)
(*     unfold h1, h2, h1', h2' in *; clear h1 h2 h1' h2'; subst. *)
(*     unfold ty, ty0 in *; clear ty ty0; subst. *)
(*     revert  H_wt H_wt0 H fi H1 H1' Rty'. *)
(*     generalize (type_of vtypes v a) as ty; *)
(*       generalize (type_of vtypes v a') as ty'; intros; subst. *)
(*     set (Z := interp vtypes v a ty') in *; clearbody Z. *)
(*     set (Z' := interp vtypes v a' ty') in *; clearbody Z'. *)
(*     destruct (has_type vtypes v a ty'); try discriminate. *)
(*     destruct (has_type vtypes v a' ty'); try discriminate. *)
(*     inversion H; subst. *)
(*     rewrite (BoolEqDep.UIP _ _ H1 H1'), (BoolEqDep.UIP_refl _ H1'). *)
(*     rewrite (BoolEqDep.UIP _ _ H_wt0 H_wt), (BoolEqDep.UIP_refl _ H_wt) in H2. *)
(*     exact (TypeEqDep.inj_pairT2 _ _ _ _ H2). *)

(*     assert (Rty := has_type_is_type_of _ _ _ _ H1). *)
(*     assert (Rty' := has_type_is_type_of _ _ _ _ H1'). *)
(*     clearbody H1 H1'; clear Hty Hty'. *)
(*     unfold h1, h2, h1', h2' in *; clear h1 h2 h1' h2'; subst. *)
(*     congruence. *)
(*   Qed. *)

(*   Property eq2_congr : forall f l l',  *)
(*     eq2_terms l l' -> eq2 (app f l) (app f l'). *)
(*   Proof. *)
(*     intros f l l' Heq. *)
(*     unfold eq2. *)
(*     assert (Teq := has_type_type_of_congr2 f l l' Heq). *)
(*     assert (icongr := fun H H' => *)
(*       interp_congr2 (type_of vtypes v (app f l)) f l l' H H' Heq). *)
(*     assert (R :=  type_of_congr2 f l l' Heq). *)
(*     do 2 decide int; subst. *)
(*     unfold ty, ty0 in *; clear ty ty0. *)
(*     admit. *)
(*     unfold ty in *; clear ty; congruence. *)
(*     unfold ty in *; clear ty; congruence. *)


(*     unfold interp'. *)
(*     revert Teq R icongr. *)
(*     generalize (type_of vtypes v (app f l)) as ty; *)
(*       generalize (type_of vtypes v (app f l')) as ty'. *)
(*     intros ty ? ? Teq icongr; subst. *)
(*     set (Z := interp vtypes v (app f l) ty) in *; clearbody Z. *)
(*     set (Z' := interp vtypes v (app f l') ty) in *; clearbody Z'. *)
(*     destruct (has_type vtypes v (app f l) ty); *)
(*       destruct (has_type vtypes v (app f l') ty); *)
(*         try discriminate; auto. *)
(*     rewrite (icongr (refl_equal _) (refl_equal _)); reflexivity. *)
(*   Qed. *)
(* End CanonicalStructure. *)
(* Print Assumptions model. *)
