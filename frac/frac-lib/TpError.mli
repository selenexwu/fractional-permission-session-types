module A = Ast
val error : A.ext -> string -> 'a
val error_unknown_var :
  string -> A.ext -> 'b
val error_unknown_var_right :
  string -> A.ext -> 'b
val error_unknown_var_ctx :
  string -> A.ext -> 'b
val error_undeclared :
  string -> A.ext -> 'a
val error_implicit : 'a -> A.ext -> 'b
val error_label_missing_alt :
  string -> A.ext -> 'a
val error_label_invalid :
  'a ->
  string * A.proto * string ->
  A.ext -> 'b
val error_label_mismatch :
  string * string -> A.ext -> 'a
val error_label_missing_branch :
  string -> A.ext -> 'a
val error_use_locked : string -> A.ext -> 'a
