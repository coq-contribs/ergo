(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

open Format
open Term
open Coqlib
open Tacmach
open Tacticals
open Tactics
open Pp
open Flags
open Locus
open Locusops
open Misctypes

type dom =
  | DomNat | DomN | DomPos | DomZ

type ty =
  | TyCst of int
  | TyDefault
  | TyArith of dom
  | TyArrow of ty * ty

type arithop =
  | Plus | Minus | Mult | Opp | Div

type symbol =
  | U of int * int
  | Cst of dom * constr
  | Op of dom * arithop

type term =
  | TApp of symbol * term list
type terms = term list

type form =
  | FVar of int
  | FEq of term * term
  | True
  | False
  | And of form * form
  | Or of form * form
  | Not of form
  | Imp of form * form
  | Iff of form * form

(* pretty-printing *)
let pr_dom fmt =   function
  | DomNat -> fprintf fmt "nat"
  | DomN -> fprintf fmt "N"
  | DomPos -> fprintf fmt "pos"
  | DomZ -> fprintf fmt "Z"
let rec pr_ty fmt = function
  | TyCst i -> fprintf fmt "%d" i
  | TyDefault -> fprintf fmt "default"
  | TyArith dom -> fprintf fmt "%a" pr_dom dom
  | TyArrow(t1, t2) -> fprintf fmt "%a -> %a" pr_ty t1 pr_ty t2
let string_of_ty ty =
  pr_ty str_formatter ty;
  flush_str_formatter ()

let pr_op fmt = function
  | Plus -> fprintf fmt "Plus"
  | Minus -> fprintf fmt "Minus"
  | Mult -> fprintf fmt "Mult"
  | Opp -> fprintf fmt "Opp"
  | Div -> fprintf fmt "Div"
let pr_symbol fmt = function
  | U(ty_idx, t_idx) ->
      fprintf fmt "U[%d, %d]" ty_idx t_idx
  | Cst(d, c) ->
      fprintf fmt "Cst<%a>" pr_dom d
  | Op(d, op) ->
      fprintf fmt "%a<%a>"pr_dom d pr_op op

let rec pr_term fmt = function
  | TApp(s, []) -> pr_symbol fmt s
  | TApp(s, l) -> fprintf fmt "%a(%a)" pr_symbol s pr_terms l
and pr_terms fmt = function
  | [] -> ()
  | [t] -> pr_term fmt t
  | t::q -> fprintf fmt "%a, %a" pr_term t pr_terms q
let string_of_term t =
  pr_term str_formatter t;
  flush_str_formatter ()

let rec pr_form fmt = function
  | FVar i -> fprintf fmt "%d" i
  | FEq(u, v) -> fprintf fmt "(%a = %a)" pr_term u pr_term v
  | True -> fprintf fmt "true"
  | False -> fprintf fmt "false"
  | And(f1,f2) -> fprintf fmt "(%a /\\ %a)" pr_form f1 pr_form f2
  | Or(f1,f2) -> fprintf fmt "(%a \\/ %a)" pr_form f1 pr_form f2
  | Not f -> fprintf fmt "~(%a)" pr_form f
  | Imp(f1,f2) -> fprintf fmt "(%a -> %a)" pr_form f1 pr_form f2
  | Iff(f1,f2) -> fprintf fmt "(%a <-> %a)" pr_form f1 pr_form f2
let string_of_form f =
  pr_form str_formatter f;
  flush_str_formatter ()

(* Coq constants *)
let coq_refl_equal () =
  Coqlib.gen_constant "Logic" ["Init";"Logic"] "refl_equal"
let coq_iff () =
  Coqlib.gen_constant "Logic" ["Init";"Logic"] "iff"
let coq_bool () =
  Coqlib.gen_constant "Datatypes" ["Init";"Datatypes"] "bool"
let coq_true () =
  Coqlib.gen_constant "Datatypes" ["Init";"Datatypes"] "true"
let coq_NNPP () =
  Coqlib.gen_constant "Classical_Prop" ["Logic";"Classical_Prop"] "NNPP"

let mk_refl_equal a x =
  mkApp (coq_refl_equal (), [|a; x|])
let mk_refl_true () =
  mk_refl_equal (coq_bool ()) (coq_true ())

let quote_const s () = Coqlib.gen_constant "Quote" ["quote";"Quote"] s
let coq_Empty = quote_const "Empty_vm"
let coq_Node = quote_const "Node_vm"
let coq_varmap_find = quote_const "varmap_find"
let coq_Right = quote_const "Right_idx"
let coq_Left = quote_const "Left_idx"
let coq_End = quote_const "End_idx"
let coq_Prop = mkProp

let coq_Rat () =
  Coqlib.gen_constant_in_modules "Rational" [["Ergo";"Rational"]] "t"

let top_const s () =
  Coqlib.gen_constant_in_modules "Ergo" [["Ergo";"Ergo"]] s
let coq_mk_varmaps = top_const "mk_varmaps"
let coq_interp = top_const "finterp"
let coq_Var = top_const "FVar"
let coq_Eq = top_const "FEq"
let coq_True = top_const "FTrue"
let coq_False = top_const "FFalse"
let coq_And = top_const "FAnd"
let coq_Or = top_const "FOr"
let coq_Not = top_const "FNot"
let coq_Imp = top_const "FImp"
let coq_Iff = top_const "FIff"
let coq_mk_abs = top_const "Build_abstraction"
let coq_abstraction = top_const "abstraction"

let term_const s () =
  Coqlib.gen_constant_in_modules "Term" [["Ergo";"Term"]] s
let coq_type = term_const "type"
let coq_tycst = term_const "typeCst"
let coq_tydef = term_const "typeDefault"
let coq_tyarith = term_const "typeArith"
let coq_tyarrow = term_const "typeArrow"
let coq_dom = term_const "arith_dom"
let coq_domNat = term_const "DomainNat"
let coq_domN = term_const "DomainN"
let coq_domPos = term_const "DomainPos"
let coq_domZ = term_const "DomainZ"
let coq_term = term_const "term"

let coq_U = term_const "Unint"
let coq_Cst = term_const "Cst"
let coq_Op = term_const "Op"
let coq_Plus = term_const "Plus"
let coq_Minus = term_const "Minus"
let coq_Mult = term_const "Mult"
let coq_Opp = term_const "Opp"
let coq_Div = term_const "Div"

let coq_app = term_const "app"
let coq_nil () =
  Coqlib.gen_constant_in_modules "List" [["Coq";"Init";"Datatypes"]] "nil"
let coq_cons () =
  Coqlib.gen_constant_in_modules "List" [["Coq";"Init";"Datatypes"]] "cons"
let coq_depvarmap = term_const "depvarmap"
let coq_depvmap = term_const "mk_depvmap"
let coq_tinterp = term_const "tinterp"
let coq_replace = term_const "replace"
let coq_teq = term_const "eq"

(* Smart constructors *)
(* let mk_varmaps v vty vsy = *)
(*   mkApp (coq_mk_varmaps (), [|mkVar v; mkVar vty; mkVar vsy|]) *)
let mk_varmaps v vty vsy =
  mkApp (coq_mk_varmaps (), [|mkVar v; mkVar vty; mkVar vsy|])
let mk_interp vm f =
  mkApp (coq_interp (), [|mkVar vm; f|])
let mk_var idx =
  mkApp (coq_Var (), [|idx|])
let mk_eq idx idx' =
  mkApp (coq_Eq (), [|idx; idx'|])
let mk_true () = coq_True ()
let mk_false () = coq_False ()
let mk_and f1 f2 =
  mkApp (coq_And (), [|f1; f2|])
let mk_or f1 f2 =
  mkApp (coq_Or (), [|f1; f2|])
let mk_not f =
  mkApp (coq_Not (), [|f|])
let mk_imp f1 f2 =
  mkApp (coq_Imp (), [|f1; f2|])
let mk_iff f1 f2 =
  mkApp (coq_Iff (), [|f1; f2|])
let mk_abs vty vsy ty ra rb =
  let r = mk_refl_true () in
  mkApp (coq_mk_abs (), [|vty; vsy; ty; ra; rb; r; r|])
let mk_abstraction vty vsy =
  mkApp (coq_abstraction (), [|vty; vsy|])

let mk_U i j =
  mkApp (coq_U (), [|i; j|])
let mk_Op d i =
  mkApp (coq_Op (), [|d; i|])
let mk_Cst d c =
  mkApp (coq_Cst (), [|d ; c|])
let mk_tapp f l =
  mkApp (coq_app (), [|f; l|])
let mk_tnil () =
  mkApp (coq_nil (), [| coq_term () |])
let mk_tcons t l =
  mkApp (coq_cons (), [| coq_term (); t; l|])
let mk_depvmap vty ty c v =
  mkApp (coq_depvmap (), [| vty; ty; c; v |])
let mk_depvarmap vty =
  mkApp (coq_depvarmap (), [| vty |])

let mk_tycst idx =
  mkApp (coq_tycst (), [|idx|])
let mk_tydef = coq_tydef
let mk_tyarith d =
  mkApp (coq_tyarith (), [|d|])
let mk_tyarrow t1 t2 =
  mkApp (coq_tyarrow (), [|t1; t2|])
let mk_tinterp vty ty =
  mkApp (coq_tinterp (), [|vty; ty|])
let mk_replace vty vsy ty a b ra rb =
  mkApp (coq_replace (), [|mkVar vty; mkVar vsy; ty; a; b; ra; rb|])
let mk_teq vty vsy ra rb =
  mkApp (coq_teq (), [|mkVar vty; mkVar vsy; ra; rb|])

let mk_left idx =
  mkApp (coq_Left (), [|idx|])
let mk_right idx =
  mkApp (coq_Right (), [|idx|])
let mk_end () = coq_End ()

(* Builds a Coq varmap corresponding to an environment *)
let varmap_of_vars ty c iter =
  let node, empty = coq_Node (), mkApp (coq_Empty (), [|ty|]) in
  if c = 0 then empty
  else
    let array = Array.make c ty in
    iter (fun frm i -> array.(i) <- frm);
    let rec build n =
      if n > c then empty
      else
	mkApp (node, [|ty; array.(n-1); build (2*n); build (2*n+1)|])
    in build 1

(* Environment for variables of a single type ;
   Parameterized by a type, a default constr of that type,
   and a default size for the hashtable
*)
module type EnvSig = sig
  val size : int
  val ty : unit -> constr
  val d : (unit -> constr) option
end
module Env (X : EnvSig) = struct
  let counter = ref 1
  let vars = Hashtbl.create X.size

  let reset () =
    Hashtbl.clear vars;
    match X.d with
      | Some d -> Hashtbl.add vars (d ()) 0; counter := 1
      | None -> counter := 0

  let add frm =
    try Hashtbl.find vars frm
    with Not_found ->
      (let n = !counter in Hashtbl.add vars frm n; incr counter; n)

  let count () = !counter

  let iter f = Hashtbl.iter f vars
  let fold f acc = Hashtbl.fold f vars acc

  let to_varmap () =
    varmap_of_vars (X.ty ()) !counter iter
end

(* Environment for propositional variables *)
module PEnv = Env (
  struct
    let size = 97
    let ty () = mkProp
    let d = Some build_coq_True
  end)

(* Environment for reified types *)
module TyEnv = Env (
  struct
    let size = 13
    let ty () = mkType (Univ.fresh_local_univ ())
    let d = None
  end)

(* Reification *)
let index_of_nat n =
  let rec digits n =
    if n = 1 then []
    else (n mod 2 = 1)::(digits (n lsr 1))
  in
    List.fold_right
      (fun b c -> (if b then mk_right else mk_left) c)
      (List.rev (digits (n+1))) (mk_end ())

let rec constr_of_dom = function
  | DomNat -> coq_domNat ()
  | DomN -> coq_domN ()
  | DomPos -> coq_domPos ()
  | DomZ -> coq_domZ ()
let rec constr_of_ty = function
  | TyCst idx -> mk_tycst (index_of_nat idx)
  | TyDefault -> mk_tydef ()
  | TyArith d -> mk_tyarith (constr_of_dom d)
  | TyArrow(t1, t2) -> mk_tyarrow (constr_of_ty t1) (constr_of_ty t2)

let rec constr_of_op = function
  | Plus -> coq_Plus ()
  | Minus -> coq_Minus ()
  | Mult -> coq_Mult ()
  | Opp -> coq_Opp ()
  | Div -> coq_Div ()
let constr_of_symbol = function
  | U(i, j) -> mk_U (index_of_nat i) (index_of_nat j)
  | Cst(d, c) -> mk_Cst (constr_of_dom d) c
  | Op(d, op) -> mk_Op (constr_of_dom d) (constr_of_op op)

let rec constr_of_term = function
  | TApp(s, l) -> mk_tapp (constr_of_symbol s) (constr_of_terms l)
and constr_of_terms = function
  | [] -> mk_tnil ()
  | t::q -> mk_tcons (constr_of_term t) (constr_of_terms q)

let rec constr_of_form = function
  | FVar i -> mk_var (index_of_nat i)
  | FEq(u, v) -> mk_eq (constr_of_term u) (constr_of_term v)
  | True -> mk_true ()
  | False -> mk_false ()
  | And(f1,f2) -> mk_and (constr_of_form f1) (constr_of_form f2)
  | Or(f1,f2) -> mk_or (constr_of_form f1) (constr_of_form f2)
  | Not f -> mk_not (constr_of_form f)
  | Imp(f1,f2) -> mk_imp (constr_of_form f1) (constr_of_form f2)
  | Iff(f1,f2) -> mk_iff (constr_of_form f1) (constr_of_form f2)

let interp_of_form vm frm =
  mk_interp vm (constr_of_form frm)

(* Environment for reified symbols *)
module TEnv = struct
  let env = Hashtbl.create 13

  let reset () =
    Hashtbl.clear env

  let add_with_type s (ty : ty) =
    let (ty_idx, (_, hty)) =
      try Hashtbl.find env ty
      with Not_found ->
	let ty_idx = Hashtbl.length env in
	let hty = Hashtbl.create 13 in
	let v = (ty_idx, (s, hty)) in
	Hashtbl.add env ty v; v
    in
    try
      (ty_idx, Hashtbl.find hty s)
    with Not_found ->
      let s_idx = Hashtbl.length hty in
      Hashtbl.add hty s s_idx;
      (ty_idx, s_idx)

  let iter f = Hashtbl.iter (fun ty (ty_idx, (_, h)) ->
			       Hashtbl.iter (f ty ty_idx) h) env
  let fold f acc = Hashtbl.fold (fun ty (ty_idx, (_, h)) acc ->
				   Hashtbl.fold (f ty ty_idx) h acc) env acc
  let to_varmap vtypes =
    let vtypes = mkVar vtypes in
    let varmap_of_hty ty s hty =
      let ty_interp = mk_tinterp vtypes ty in
      mk_depvmap vtypes ty s
	(varmap_of_vars ty_interp (Hashtbl.length hty)
	   (fun f -> Hashtbl.iter f hty))
    in
    varmap_of_vars (mk_depvarmap vtypes) (Hashtbl.length env)
      (fun f -> Hashtbl.iter (fun ty (ty_idx, (s, hty)) ->
				f (varmap_of_hty (constr_of_ty ty) s hty)
				  ty_idx) env)
end

let rec assoc_constr c = function
  | [] -> raise Not_found
  | (a, b)::q when eq_constr a c -> b
  | _::q -> assoc_constr c q

let rec reify_types res = function
  | [] -> res
  | ty::q -> TyArrow(ty, reify_types res q)
let reify_type ty =
  try
    TyArith
      (assoc_constr ty
	 [(Lazy.force Arith.coq_nat, DomNat);
	  (Lazy.force Arith.coq_N, DomN);
	  (Lazy.force Arith.coq_positive, DomPos);
	  (Lazy.force Arith.coq_Z, DomZ)])
  with Not_found -> TyCst (TyEnv.add ty)

let reify_symbol h hty =
  try
    assoc_constr h
      [	(Lazy.force Arith.coq_plus, Op(DomNat, Plus));
	(Lazy.force Arith.coq_mult, Op(DomNat, Mult));

	(Lazy.force Arith.coq_Nplus, Op(DomN, Plus));
	(Lazy.force Arith.coq_Nmult, Op(DomN, Mult));

	(Lazy.force Arith.coq_Pplus, Op(DomPos, Plus));
	(Lazy.force Arith.coq_Pmult, Op(DomPos, Mult));

	(Lazy.force Arith.coq_Zplus, Op(DomZ, Plus));
	(Lazy.force Arith.coq_Zminus, Op(DomZ, Minus));
	(Lazy.force Arith.coq_Zmult, Op(DomZ, Mult));
	(Lazy.force Arith.coq_Zopp, Op(DomZ, Opp))
      ]
  with Not_found ->
    let (ty_idx, t_idx) = TEnv.add_with_type h hty in
      U(ty_idx, t_idx)

let is_constant env t =
  let ty = Typing.type_of env Evd.empty t in
  let d, test =
    match ty with
      | _ when eq_constr ty (Lazy.force Arith.coq_nat) ->
	  DomNat, Arith.is_nat_constant
      | _ when eq_constr ty (Lazy.force Arith.coq_N) ->
	  DomN, Arith.is_N_constant
      | _ when eq_constr ty (Lazy.force Arith.coq_positive) ->
	  DomPos, Arith.is_positive_constant
      | _ when eq_constr ty (Lazy.force Arith.coq_Z) ->
	  DomZ, Arith.is_Z_constant
      | _ -> DomNat, fun _ -> false
  in
    if test t then Some d else None

let rec reify_term env t =
  match is_constant env t with
    | Some d -> TyArith d, TApp (Cst(d, t), [])
    | None ->
	let h, l = decompose_app t in
	let ty = Typing.type_of env Evd.empty h in
	let _, tyres = decompose_prod_n (List.length l) ty in
	let lty, lreif = List.split (List.map (reify_term env) l) in
	let res = reify_type tyres in
	let hty = reify_types res lty in
	let hreif = reify_symbol h hty in
	  res, TApp (hreif, lreif)

let rec reify env with_terms acc frm =
  let reify = reify env with_terms in
  match kind_of_term frm with
    | Prod (_,f1,f2) when not (Termops.dependent (mkRel 1) f2) ->
	let acc1, rf1 = reify acc f1 in
	let acc2, rf2 = reify acc1 f2 in
	acc2, Imp (rf1, rf2)
    | _ ->
	let hs, args = decompose_app frm in
	  match args with
	    | [] when eq_constr hs (build_coq_False ()) -> acc, False
	    | [] when eq_constr hs (build_coq_True ()) -> acc, True
	    | [f] when eq_constr hs (build_coq_not ()) ->
		let acc1, rf = reify acc f in
		acc1, Not rf
	    | [f1; f2] when eq_constr hs (build_coq_or ()) ->
		let acc1, rf1 = reify acc f1 in
		let acc2, rf2 = reify acc1 f2 in
		acc2, Or (rf1, rf2)
	    | [f1; f2] when eq_constr hs (build_coq_and ()) ->
		let acc1, rf1 = reify acc f1 in
		let acc2, rf2 = reify acc1 f2 in
		acc2, And (rf1, rf2)
	    | [f1; f2] when eq_constr hs (coq_iff ()) ->
		let acc1, rf1 = reify acc f1 in
		let acc2, rf2 = reify acc1 f2 in
		acc2, Iff (rf1, rf2)
	    | [t;a;b] when with_terms && hs = build_coq_eq () ->
		let ty, ra = reify_term env a in
		let _, rb = reify_term env b in
		(t, ty, a, b, ra, rb)::acc, FEq (ra, rb)
	    | _ ->  acc, FVar (PEnv.add frm)

(* print_props and quote_props *)
let print_props vm_name gl =
  Coqlib.check_required_library ["Coq";"quote";"Quote"];
  Coqlib.check_required_library ["Ergo";"Ergo"];
  PEnv.reset (); TyEnv.reset (); TEnv.reset ();
  let env = pf_env gl in
  let varmap_name =
    fresh_id [] (Names.id_of_string "_varmap__v") gl in
  let vtypes_name =
    fresh_id [] (Names.id_of_string "_vtypes__v") gl in
  let vsymbols_name =
    fresh_id [] (Names.id_of_string "_vsymbols__v") gl in
  let (lid, rews, lch) =
    List.fold_left
      (fun (acc, rews, lch) (id,ty) ->
	 match kind_of_term (Typing.type_of env Evd.empty ty) with
	   | Sort (Prop Null) ->
	       let rews, rf = reify env true rews ty in
	       let s = Format.sprintf "%s : %s"
		 (Names.string_of_id id) (string_of_form rf) in
	       ((str s) ++ (fnl ()) ++ acc,
		rews,
		(id,
		 interp_of_form vm_name rf)::lch)
	   | _ -> acc, rews, lch)
      ((str "are the propositional statements in the context.") ++ (fnl ()),
       [],
       [])
      (pf_hyps_types gl) in
  let senv =
    PEnv.fold
      (fun frm i acc ->
	 let s = Printf.sprintf "%d : " i in
	 (str s) ++ (Termops.print_constr frm) ++ (fnl ()) ++ acc)
      ((str "are the propositions the variables map to.") ++ (fnl ())) in
  let sty =
    TyEnv.fold
      (fun ty ty_idx acc ->
	 let msg = Format.sprintf "%d : " ty_idx in
	 (str msg) ++ (Termops.print_constr ty) ++ (fnl ()) ++ acc)
      ((str "are the types the type variables map to.") ++ (fnl ())) in
  let ssymb =
    TEnv.fold
      (fun ty ty_idx s s_idx acc ->
	 let msg = Format.sprintf "[%d, %d] = " ty_idx s_idx in
	 (str msg) ++ (Termops.print_constr s) ++
	   (str " : ") ++ (str (string_of_ty ty)) ++ (fnl ()) ++ acc)
      ((str "are the symbols the variables map to.") ++ (fnl ())) in
  let srews =
    List.fold_left
      (fun acc (_, ty, a, b, ra, rb) ->
	 let msg = Format.sprintf "%s : %s = %s <-> "
	   (string_of_ty ty) (string_of_term ra) (string_of_term rb) in
	 (str msg) ++ (Termops.print_constr a) ++
	   (str " = ") ++ (Termops.print_constr b) ++ (fnl ()) ++ acc)
      ((str "are the equations that should be rewritten.") ++ (fnl ())) rews in
  let tacch =
    let n id =
      Names.Name (Names.id_of_string ((Names.string_of_id id)^"_reif")) in
    tclTHENSEQ
      (List.map (fun (id, c) -> letin_tac None (n id) c None onConcl) lch) in
  let tac =
    tclTHEN tacch (tclIDTAC_MESSAGE (lid ++ senv ++ sty ++ ssymb ++ srews)) in
  let v = PEnv.to_varmap () in
  let vty = TyEnv.to_varmap () in
  let vsy = TEnv.to_varmap vtypes_name in
  let vm = mk_varmaps varmap_name vtypes_name vsymbols_name
  in
    (tclTHEN (letin_tac None (Names.Name varmap_name) v None onConcl)
       (tclTHEN (letin_tac None (Names.Name vtypes_name) vty None onConcl)
	  (tclTHEN (letin_tac None (Names.Name vsymbols_name) vsy None onConcl)
	     (tclTHEN (letin_tac None (Names.Name vm_name) vm None onConcl)
		tac)))) gl

let quote_props vm_name gl =
  Coqlib.check_required_library ["Coq";"quote";"Quote"];
  Coqlib.check_required_library ["Ergo";"Ergo"];
  PEnv.reset (); TyEnv.reset (); TEnv.reset ();
  let env = pf_env gl in
  let varmap_name =
    fresh_id [] (Names.id_of_string "_varmap__v") gl in
  let vtypes_name =
    fresh_id [] (Names.id_of_string "_vtypes__v") gl in
  let vsymbols_name =
    fresh_id [] (Names.id_of_string "_vsymbols__v") gl in
  let lch =
    List.fold_left
      (fun lch (id,ty) ->
	 match kind_of_term (Typing.type_of env Evd.empty ty) with
	   | Sort (Prop Null) ->
	       (id, interp_of_form vm_name (snd (reify env false [] ty)))::lch
	   | _ -> lch)
      [] (pf_hyps_types gl) in
  let tacch =
    tclTHENSEQ (List.map (fun (id, c) -> convert_hyp (id, None, c)) lch) in
  let v = PEnv.to_varmap () in
  let vty = TyEnv.to_varmap () in
  let vsy = TEnv.to_varmap vtypes_name in
  let vm = mk_varmaps varmap_name vtypes_name vsymbols_name in
  (tclTHEN (letin_tac None (Names.Name varmap_name) v None onConcl)
     (tclTHEN (letin_tac None (Names.Name vtypes_name) vty None onConcl)
	(tclTHEN (letin_tac None (Names.Name vsymbols_name) vsy None onConcl)
	   (tclTHEN (letin_tac None (Names.Name vm_name) vm None onConcl)
	      tacch)))) gl

let quote_everything vm_name gl =
  Coqlib.check_required_library ["Coq";"quote";"Quote"];
  Coqlib.check_required_library ["Ergo";"Ergo"];
  PEnv.reset (); TyEnv.reset (); TEnv.reset ();
  let env = pf_env gl in
  let varmap_name =
    fresh_id [] (Names.id_of_string "_varmap__v") gl in
  let vtypes_name =
    fresh_id [] (Names.id_of_string "_vtypes__v") gl in
  let vsymbols_name =
    fresh_id [] (Names.id_of_string "_vsymbols__v") gl in
  let lch =
    List.fold_left
      (fun lch (id,ty) ->
	 match kind_of_term (Typing.type_of env Evd.empty ty) with
	   | Sort (Prop Null) ->
	       let rews, rf = reify env true [] ty in
	       let interp_rf = interp_of_form vm_name rf in
		 ((id, interp_rf, rews)::lch)
	   | _ -> lch)
      []
      (pf_hyps_types gl) in
  let v = PEnv.to_varmap () in
  let vty = TyEnv.to_varmap () in
  let vsy = TEnv.to_varmap vtypes_name in
  let vm = mk_varmaps varmap_name vtypes_name vsymbols_name in
  let rewtactic id (t, ty, a, b, ra, rb) : Proof_type.tactic =
    let r = fresh_id [] (Names.id_of_string "rew") gl in
    let cra = constr_of_term ra in
    let crb = constr_of_term rb in
    let rw =
      mk_replace vtypes_name vsymbols_name (constr_of_ty ty)
	a b cra crb in
    let byapp =
      tclTHEN (apply rw) (tclTHEN simpl_in_concl reflexivity) in
    let cut =
      mkApp (coq_iff (), [|
	       mkApp (build_coq_eq (), [|t; a; b|]);
	       mk_teq vtypes_name vsymbols_name cra crb |]) in
      tclTHEN (assert_by (Names.Name r) cut byapp)
	(tclTHEN (Equality.general_rewrite_in
		    true AllOccurrences false true id (mkVar r) false)
	   (clear [r]))
  in
  let rews (id, _, rs) = List.map (rewtactic id) rs in
(*   let tacch = *)
(*     let n id = *)
(*       Names.Name (Names.id_of_string ((Names.string_of_id id)^"_reif")) in *)
(*     tclTHENSEQ  *)
(*       (List.map (fun (id, c, _) ->  *)
(* 		   letin_tac None (n id) c None onConcl) lch) in *)
  let tacch =
    tclTHENSEQ (List.map (fun ((id, c, _) as e) ->
			    tclTHEN (tclTHENSEQ (rews e))
			      (convert_hyp (id, None, c))) lch) in
  (tclTHEN (letin_tac None (Names.Name varmap_name) v None onConcl)
     (tclTHEN (letin_tac None (Names.Name vtypes_name) vty None onConcl)
	(tclTHEN (letin_tac None (Names.Name vsymbols_name) vsy None onConcl)
	   (tclTHEN (letin_tac None (Names.Name vm_name) vm None onConcl)
	      tacch)))) gl


(* ERGO REIFY, NEW VERSION *)
let build_conjunction finalid gl =
  let env = pf_env gl in
  let prop_hyps =
    List.filter
      (fun (id,ty) ->
	 match kind_of_term (Typing.type_of env Evd.empty ty) with
	   | Sort (Prop Null) -> true
	   | _ -> false
      )
      (pf_hyps_types gl)
  in
  let (conj, _, lids) =
    match prop_hyps with
      | [] -> (build_coq_I (), build_coq_True (), [])
      | (ida, hypa)::q ->
	  List.fold_left (fun (acct, accf, accids) (id, hyp) ->
			    (mkApp (build_coq_conj (),
				    [|accf; hyp; acct; mkVar id|]),
			     mkApp (build_coq_and (), [|accf; hyp|]),
			     id::accids
			    ))
	    (mkVar ida, hypa, [ida]) q
  in
    (tclTHEN (pose_proof (Names.Name finalid) conj) (clear lids)) gl

let ergo_reify f_id reif_id vm_id gl =
  Coqlib.check_required_library ["Coq";"quote";"Quote"];
  Coqlib.check_required_library ["Ergo";"Ergo"];
  PEnv.reset (); TyEnv.reset (); TEnv.reset ();
  let env = pf_env gl in
  let fresh s = pf_get_new_id (Names.id_of_string s) gl in
  let v_id = fresh "_varmap__v" in
  let vty_id = fresh "_vtypes__v" in
  let vsy_id = fresh "_vsymbols__v" in
  let let_def id c =
    letin_tac None (Names.Name id) c None onConcl in
  let let_defs lid lc =
    tclTHENSEQ (List.map2 let_def lid lc) in
  let fty = pf_get_hyp_typ gl f_id in
    match kind_of_term (Typing.type_of env Evd.empty fty) with
      | Sort (Prop Null) ->
	  let _, rf = reify env true [] fty in
	  let creif = constr_of_form rf in
	  let v = PEnv.to_varmap () in
	  let vty = TyEnv.to_varmap () in
	  let vsy = TEnv.to_varmap vty_id in
	  let vm = mk_varmaps v_id vty_id vsy_id in
	    (let_defs
	       [v_id; vty_id; vsy_id; vm_id; reif_id]
	       [v; vty; vsy; vm; creif]) gl
      | k ->
	  let pps =
	    (str (" Cannot reify "^(Names.string_of_id f_id)^": its type "))
	    ++ (Termops.print_constr fty)
	    ++ (str " is not of type Prop") in
	    tclFAIL 0 pps gl

(* Requiring check and applying double negation *)
let valid_prepare gl =
  let tac =
    try (Coqlib.check_required_library ["Coq";"Logic";"Classical_Prop"];
	 apply (coq_NNPP ()))
    with _ ->
      let msg =
	(str  "To use [valid] in order to prove the validity\n"
	 ++ str " of a formula, you need classical logic in general. Try\n"
	 ++ str " Require Import Classical. If you don't want to assume\n"
	 ++ str " classical logic and your goal is decidable, try applying\n"
	 ++ str " double negation first and then use the [unsat] Ergo tactic")
      in
	tclFAIL 2 msg
  in
    tac gl

(* Printing facilities *)
let print_array f sep fin fmt a =
  Array.iter (fun i -> fprintf fmt "%a%s" f i sep) a;
  fprintf fmt "%s@." fin

let string_of_name name =
  match name with
    | Names.Anonymous -> "anonymous"
    | Names.Name n -> Names.string_of_id n

let print_kn fmt kn =
  fprintf fmt "%s" (Names.string_of_con (Names.constant_of_kn kn))

let rec print_constr fmt c =
  let f = print_constr in
  match kind_of_term c with
  | _ when c = build_coq_False () -> fprintf fmt "False"
  | _ when c = build_coq_True () -> fprintf fmt "True"
  | _ when c = build_coq_not () -> fprintf fmt "Not"
  | _ when c = build_coq_or () -> fprintf fmt "Or"
  | _ when c = build_coq_and () -> fprintf fmt "And"
  | Rel i -> fprintf fmt "rel %d" i
  | Var id -> fprintf fmt ("var %s") (Names.string_of_id id)
  | Meta _ -> fprintf fmt "meta"
  | Evar (i, constr_array) ->
      fprintf fmt "Evar : %d %a" i (print_array f " " "") constr_array
  | Sort s ->
      (match s with
	 | Prop Null -> fprintf fmt "sort(prop)"
	 | Prop Pos -> fprintf fmt "sort(set)"
	 | Type _ -> fprintf fmt "sort(type)")
  | Cast (term, _, typ) ->
      fprintf fmt "cast du term %a avec le type %a" f term f typ
  | Prod (name, typ, typ') ->
      fprintf fmt "Prod (%s * %a * {%a})" (string_of_name name) f typ f typ'
  | Lambda (name, typ, constr) ->
      fprintf fmt "Lambda (%s : %a=%a)"
	(string_of_name name) f typ f constr
  | LetIn (name, constr,typ, constr') ->
      fprintf fmt "Let %s : %a = %a in %a@."
	(string_of_name name) f typ f constr f constr'
  | App (constr, constr_array) ->
      fprintf fmt "%a @ (%a)" f constr (print_array f ", " "") constr_array
  | Const const ->
      fprintf fmt "constante %s" (Names.string_of_con const)
  | Ind(mult_ind, i) ->
      fprintf fmt "Ind (%a, %d)" print_kn (Names.user_mind mult_ind) i
  | Construct ((mult_ind, i), i')->
      fprintf fmt "Constructor ((%a, %d), %d)"
	print_kn (Names.user_mind mult_ind) i i'
  | Case (case_info, constr, constr', constr_array) ->
      fprintf fmt "match %a as %a with @.%a end" f constr f constr'
	(print_array f "\n" "") constr_array
  | Fix ((int_array, int),(name_a, type_a, constr_a)) ->
      fprintf fmt "fix %d, %d\n %a\n %a\n %a@."
	(Array.length int_array) int
	(print_array (fun fmt s ->
			fprintf fmt "%s" (string_of_name s)) ", " "")
	name_a
	(print_array f ", " "") type_a
	(print_array f ", " "") constr_a
  | CoFix (int, (name_a, type_a, constr_a)) ->
      fprintf fmt "cofix %d\n %a\n %a\n %a@."
	int
	(print_array (fun fmt s ->
			fprintf fmt "%s" (string_of_name s)) ", " "")
	name_a
	(print_array f ", " "") type_a
	(print_array f ", " "") constr_a

let print_ast constr_expr =
  let constr =
    Constrintern.interp_constr Evd.empty (Global.env ()) constr_expr in
    fprintf std_formatter "%a" print_constr constr

(* Toplevel Extensions *)

TACTIC EXTEND print_props
  [ "print_props" ident(id) ] -> [ print_props id ]
END

TACTIC EXTEND quote_props
  [ "quote_props" ident(id) ] -> [ quote_props id ]
END

TACTIC EXTEND quote_everything
  [ "quote_everything" ident(id) ] -> [ quote_everything id ]
END

TACTIC EXTEND build_conjunction
  [ "build_conjunction" ident(id) ] -> [ build_conjunction id ]
END

TACTIC EXTEND ergo_reify
  [ "ergo_reify" ident(f) ident(reif) ident(v) ] ->
    [ ergo_reify f reif v ]
END

TACTIC EXTEND valid_prepare
  [ "valid_prepare" ] ->
    [ valid_prepare ]
END

VERNAC COMMAND EXTEND PrintTerm CLASSIFIED AS QUERY
 ["PrintAst" constr(constr_expr)] ->
    [ print_ast constr_expr ]
END
