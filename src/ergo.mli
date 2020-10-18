val print_props : Names.Id.t -> unit Proofview.tactic
val quote_props : Names.Id.t -> unit Proofview.tactic
val quote_everything : Names.Id.t -> unit Proofview.tactic

val build_conjunction : Names.Id.t -> unit Proofview.tactic
val ergo_reify : Names.Id.t -> Names.Id.t ->
  Names.Id.t -> unit Proofview.tactic

val print_constr : Format.formatter -> Constr.t -> unit
val print_ast : Constrexpr.constr_expr -> unit
