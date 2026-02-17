module R = Arith
module A = Ast
val pp_arith : R.arith -> string
val pp_tp_simple : A.stype -> string
val pp_proto_simple : A.proto -> string
val pp_chan : string -> string
[@@deprecated "is identity function"]
val pp_channames : string list -> string
val pp_proto : 'a -> A.proto -> A.tpname
val pp_lsctx : 'a -> (string * A.proto) list -> string
val pp_tpj_compact :
  'a ->
  A.context -> string * A.proto -> string
val pp_exp_prefix : 'a A.st_expr -> string
val pp_decl : 'a -> A.decl -> string
val pp_prog : (A.decl * 'a) list -> string
val pp_chantp_list : A.chan_tp list -> string
val pp_perm : A.perm -> string
val pp_perms : A.perm list -> string
