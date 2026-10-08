(* Syntax *)
(* Explicit syntax performs no reconstruction
* Implicit syntax reconstructs most FracST constructs
*)
type syntax = Implicit | Explicit

let parseSyntax s =
  match s with
  | "implicit" ->
      Some Implicit
  | "explicit" ->
      Some Explicit
  | _ ->
      None

let pp_syntax syn =
  match syn with Implicit -> "implicit" | Explicit -> "explicit"

(* Default values *)
let syntax = ref Explicit

let verbosity =
  ref 0 (* -1 = print nothing, 0 = quiet, 1 = normal, 2 = verbose, 3 = debug *)

let reset () =
  syntax := Explicit ;
  verbosity := 0 ;
