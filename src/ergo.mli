val print_props : Names.identifier -> Proof_type.tactic
val quote_props : Names.identifier -> Proof_type.tactic
val quote_everything : Names.identifier -> Proof_type.tactic

val build_conjunction : Names.identifier -> Proof_type.tactic
val ergo_reify : Names.identifier -> Names.identifier ->
  Names.identifier -> Proof_type.tactic

val print_constr : Format.formatter -> Term.constr -> unit
val print_ast : Topconstr.constr_expr -> unit
