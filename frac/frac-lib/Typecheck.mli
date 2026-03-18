module A = Ast
(* val esync_tp :
     (A.decl * 'a) list ->
     A.stype -> ((int * int) * (int * int) * string) option -> unit
   val ssync_tp :
     (A.decl * 'a) list ->
     A.stype -> ((int * int) * (int * int) * string) option -> unit *)
val contractive : A.proto -> bool
val is_tpdef : (A.decl * 'a) list -> string -> bool
val is_expdecdef : (A.decl * 'a) list -> string -> bool
val check_declared : (A.decl * 'a) list -> A.ext -> A.proto -> unit
val check_declared_list : (A.decl * 'a) list -> A.ext -> A.chan_tp list -> unit
val checkexp :
  bool ->
  (A.decl * 'a) list ->
  A.context ->
  A.ext A.st_aug_expr -> A.chan * A.proto -> A.ext -> A.cont -> unit
(* val link_tps :
     (A.decl * 'a) list ->
     (A.chan, A.stype, 'b) Core.Map.t ->
     'c A.arg list ->
     A.argument list -> ((int * int) * (int * int) * string) option -> unit
   val pure :
     'a ->
     string ->
     A.context ->
     A.str * string * A.mode ->
     ((int * int) * (int * int) * string) option -> unit
   val shared :
     'a ->
     string ->
     A.context ->
     A.str * string * A.mode ->
     ((int * int) * (int * int) * string) option -> unit
   val transaction :
     'a ->
     string ->
     A.context ->
     A.str * string * A.mode ->
     ((int * int) * (int * int) * string) option -> unit *)
