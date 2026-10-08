type syntax = Implicit | Explicit

val parseSyntax : string -> syntax option

val pp_syntax : syntax -> string

val syntax : syntax ref

val verbosity : int ref

val reset : unit -> unit
