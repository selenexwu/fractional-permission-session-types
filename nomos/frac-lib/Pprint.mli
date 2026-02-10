module R = Arith
module A = Ast
val pp_arith : R.arith -> string
val pp_tp_simple : A.stype -> string
val pp_proto_simple : A.proto -> string
val pp_chan : string -> string
val pp_channames : string list -> string
val pp_tp : 'a -> A.proto -> A.tpname
val pp_tp_compact : 'a -> A.proto -> A.tpname
val pp_lsctx : 'a -> (string * A.proto) list -> string
val pp_tpj_compact :
  'a ->
  A.chan_tp list -> string * A.proto -> string
val pp_exp_prefix : 'a A.st_expr -> string
val pp_decl : 'a -> A.decl -> string
val pp_prog : (A.decl * 'a) list -> string
