module A = Ast

val valid_implicit_top_type : (A.decl * 'a) list -> A.proto -> bool

val contractive : A.proto -> bool

val is_tpdef : (A.decl * 'a) list -> string -> bool

val is_expdecdef : (A.decl * 'a) list -> string -> bool

val check_declared : (A.decl * 'a) list -> A.ext -> A.proto -> unit

val check_declared_list : (A.decl * 'a) list -> A.ext -> A.chan_tp list -> unit

val checkexp :
     bool
  -> (A.decl * 'a) list
  -> A.context
  -> A.ext A.st_aug_expr
  -> A.chan * A.proto
  -> A.ext
  -> A.cont
  -> unit

val check_decls : (A.decl * 'a) list -> (A.decl * A.ext) list -> unit

val check_redecl :
  (A.decl * ((int * int) * (int * int) * string) option) list -> unit

val check_valid : (A.decl * 'a) list -> (A.decl * A.ext) list -> unit
