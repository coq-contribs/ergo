open Term
open Coqlib

(* arithmetic constants *)
let gen_in_nat t = lazy (gen_constant "Datatypes" ["Init"; "Datatypes"] t)
let gen_in_peano t = lazy (gen_constant "Peano" ["Init"; "Peano"] t)
let coq_nat = gen_in_nat "nat"
let coq_S = gen_in_nat "S"
let coq_O = gen_in_nat "O"
let coq_pred = gen_in_peano "pred"
let coq_plus = gen_in_peano "plus"
let coq_mult = gen_in_peano "mult"

let gen_in_nums t = lazy (gen_constant "BinNums" ["Numbers"; "BinNums"] t)

let gen_in_pos t = lazy (gen_constant "BinPos" ["PArith"; "BinPos";"Pos"] t)
let coq_positive = gen_in_nums "positive"
let coq_xO = gen_in_nums "xO"
let coq_xI = gen_in_nums "xI"
let coq_xH = gen_in_nums "xH"
let coq_Psucc = gen_in_pos "succ"
let coq_P_of_succ_nat = gen_in_pos "of_succ_nat"
let coq_Pdouble_minus_one = gen_in_pos "pred_double"
let coq_Ppred = gen_in_pos "pred"
let coq_Pplus = gen_in_pos "add"
let coq_Pmult = gen_in_pos "mul"

let gen_in_N t = lazy (gen_constant "BinNat" ["NArith"; "BinNat";"N"] t)
let coq_N = gen_in_nums "N"
let coq_N0 = gen_in_nums "N0"
let coq_Npos = gen_in_nums "Npos"
let coq_Nplus = gen_in_N "add"
let coq_Nmult = gen_in_N "mul"

let gen_in_Z t = lazy (gen_constant "BinInt" ["ZArith"; "BinInt";"Z"] t)
let coq_Z = gen_in_nums "Z"
let coq_Z0 =  gen_in_nums "Z0"
let coq_Zpos = gen_in_nums "Zpos"
let coq_Zneg = gen_in_nums "Zneg"
let coq_Zplus = gen_in_Z "add"
let coq_Zminus = gen_in_Z "sub"
let coq_Zopp = gen_in_Z "opp"
let coq_Zmult = gen_in_Z "mul"

(** constants that could be added **)
(* Zdouble_plus_one: Z -> Z *)
(* Zdouble_minus_one: Z -> Z *)
(* Zdouble: Z -> Z *)
(* ZPminus: positive -> positive -> Z *)
(* Zsucc: Z -> Z *)
(* Zpred: Z -> Z *)
(* Zsgn: Z -> Z *)
(* Zsucc': Z -> Z *)
(* Zpred': Z -> Z *)
(* Zplus': Z -> Z -> Z *)
(* Zabs: Z -> Z *)
(* Z_of_nat: nat -> Z *)
(* Z_of_N: N -> Z *)
(* Z_of_nat': nat -> Z *)
(* Zpos': positive -> Z *)
(* Zneg': positive -> Z *)
(* Z_of_N': N -> Z *)
(* ZOdiv_def.ZOdiv: Z -> Z -> Z *)
(* ZOdiv_def.ZOmod: Z -> Z -> Z *)
(* floor: positive -> Z *)
(* Zdiv: Z -> Z -> Z *)
(* Zmod: Z -> Z -> Z *)
(* Zmod_POS: positive -> Z -> Z *)
(* Zmod': Z -> Z -> Z *)
(* Zdiv2: Z -> Z *)
(* log_inf: positive -> Z *)
(* log_sup: positive -> Z *)
(* log_near: positive -> Z *)
(* N_digits: Z -> Z *)
(* Zmax: Z -> Z -> Z *)
(* Zmin: Z -> Z -> Z *)
(* Zpower_pos: Z -> positive -> Z *)
(* Zpower: Z -> Z -> Z *)
(* Zpower_nat: Z -> nat -> Z *)
(* two_power_nat: nat -> Z *)
(* two_power_pos: positive -> Z *)
(* two_p: Z -> Z *)
(* Zsqrt_plain: Z -> Z   *)

(* reified types *)
type 'a reified =
  | Constant of constr
  | NotConstant of constr * 'a

(* reification *)
let rec is_nat_constant t =
  let hs, l = decompose_app t in
    match l with
      | [] when eq_constr hs (Lazy.force coq_O) -> true
      | [n] when eq_constr hs (Lazy.force coq_S) -> is_nat_constant n
      | [n] when eq_constr hs (Lazy.force coq_pred) -> is_nat_constant n
      | [m; n] when eq_constr hs (Lazy.force coq_plus)
	  || eq_constr hs (Lazy.force coq_mult)
	  -> is_nat_constant m && is_nat_constant m
      | _ -> false

let reify_nat t =
  let rec reif t acc =
    let hs, l = decompose_app t in
      match l with
	| [] when eq_constr hs (Lazy.force coq_O) -> Constant acc
	| [n] when eq_constr hs (Lazy.force coq_S) ->
	    begin
	      match reif t acc with
		| (Constant _) as acc -> acc
		| NotConstant (t, k) -> NotConstant (t, k+1)
	    end
	| [n] when eq_constr hs (Lazy.force coq_pred) ->
	    if is_nat_constant n then Constant acc
	    else NotConstant (t, 0)
	| _ -> NotConstant (t, 0)
  in
    reif t t

let rec is_positive_constant t =
  let hs, l = decompose_app t in
    match l with
      | [] when eq_constr hs (Lazy.force coq_xH) -> true
      | [n] when eq_constr hs (Lazy.force coq_xO) -> is_positive_constant n
      | [n] when eq_constr hs (Lazy.force coq_xI) -> is_positive_constant n
      | [n] when eq_constr hs (Lazy.force coq_Psucc)
	  || eq_constr hs (Lazy.force coq_P_of_succ_nat)
	  || eq_constr hs (Lazy.force coq_Pdouble_minus_one)
	  || eq_constr hs (Lazy.force coq_Ppred) ->
	  is_positive_constant n
      | [n; m] when eq_constr hs (Lazy.force coq_Pplus)
	  || eq_constr hs (Lazy.force coq_Pmult) ->
	  is_positive_constant n && is_positive_constant m
      | _ -> false

let reify_positive t0 =
  let rec reif t =
    let hs, l = decompose_app t in
      match l with
	| [] when eq_constr hs (Lazy.force coq_xH) -> Constant t0
	| [n] when eq_constr hs (Lazy.force coq_xO) -> reif n
	| [n] when eq_constr hs (Lazy.force coq_xI) -> reif n
	| [n] when eq_constr hs (Lazy.force coq_Psucc) -> reif n
	| [n] when eq_constr hs (Lazy.force coq_P_of_succ_nat) ->
	    if is_nat_constant n then Constant t0 else NotConstant (t0, 0)
	| [n] when eq_constr hs (Lazy.force coq_Pdouble_minus_one) ->
	    reif n
	| [n] when eq_constr hs (Lazy.force coq_Ppred) ->
	    reif n
	| _ -> NotConstant (t0, 0)
  in
    reif t0

let rec is_N_constant t =
  let hs, l = decompose_app t in
    match l with
      | [] when eq_constr hs (Lazy.force coq_N0) -> true
      | [n] when eq_constr hs (Lazy.force coq_Npos) -> is_positive_constant n
      | _ -> false
let reify_N t0 =
  let rec reif t =
    let hs, l = decompose_app t in
      match l with
	| [] when eq_constr hs (Lazy.force coq_N0) -> Constant t0
	| [n] when eq_constr hs (Lazy.force coq_Npos) ->
	    if is_positive_constant n then Constant t0
	    else NotConstant (t0, 0)
	| _ -> NotConstant (t0, 0)
  in
    reif t0

(* Ajouter plus de constructeurs de constantes *)
let rec is_Z_constant t =
  let hs, l = decompose_app t in
    match l with
      | [] when eq_constr hs (Lazy.force coq_Z0) -> true
      | [n] when eq_constr hs (Lazy.force coq_Zpos) -> is_positive_constant n
      | [n] when eq_constr hs (Lazy.force coq_Zneg) -> is_positive_constant n
      | _ -> false
let reify_Z t0 =
  let rec reif t =
    let hs, l = decompose_app t in
      match l with
	| [] when eq_constr hs (Lazy.force coq_Z0) -> Constant t0
	| [n] when eq_constr hs (Lazy.force coq_Zpos) ->
	    if is_positive_constant n then Constant t0
	    else NotConstant (t0, 0)
	| [n] when eq_constr hs (Lazy.force coq_Zneg) ->
	    if is_positive_constant n then Constant t0
	    else NotConstant (t0, 0)
	| _ -> NotConstant (t0, 0)
  in
    reif t0
