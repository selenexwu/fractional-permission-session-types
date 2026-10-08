module C = Core
module CU = Core_unix
module TL = Lib.TopLevel
module PP = Lib.Pprint
module F = Lib.FracstFlags
module EM = Lib.ErrorMsg

let error m = EM.error EM.Pragma None m

let check_extension filename ext =
  if Filename.check_suffix filename ext then filename
  else
    EM.error EM.File None
      ("'" ^ filename ^ "' does not have " ^ ext ^ " extension!\n")

let set_syntax s =
  match F.parseSyntax s with
  | None ->
      error ("% syntax " ^ s ^ " not recognized\n")
  | Some syn ->
      F.syntax := syn

let file (ext : string) =
  C.Command.Arg_type.create (fun filename ->
      if Sys.is_regular_file filename then check_extension filename ext
      else EM.error EM.File None ("'" ^ filename ^ "' is not a regular file!\n") )

let frac_file = file ".frac"

let frac_command =
  C.Command.basic ~summary:"Typechecking FracST files"
    C.Command.Let_syntax.(
      let%map_open verbosity =
        flag "-v"
          (optional_with_default 0 int)
          ~doc:"verbosity:- 0: quiet, 1: default, 2: verbose, 3: debugging mode"
      and syntax =
        flag "-s"
          (optional_with_default "explicit" string)
          ~doc:"syntax: implicit, explicit"
      and file = anon ("filename" %: frac_file) in
      fun () ->
        let raw = TL.read file in
        F.verbosity := verbosity ;
        set_syntax syntax ;
        let _txn = TL.check raw in
        () )

let () = Command_unix.run ~version:"1.0" ~build_info:"stable" frac_command
