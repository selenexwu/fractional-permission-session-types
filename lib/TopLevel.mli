module A = Ast

type environment = (A.decl * A.ext) list

(* read an environment from a file *)
val read : string -> environment

val check : environment -> unit
