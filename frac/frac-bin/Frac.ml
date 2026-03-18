(* module NC = Lib.NomosConfig *)
module C = Core
module TL = Lib_frac.TopLevel
module PP = Lib_frac.Pprint
module F = Lib_frac.FracFlags
module EM = Lib_frac.ErrorMsg

let check_extension filename ext =
  if Filename.check_suffix filename ext
  then filename
  else
    EM.error EM.File None ("'" ^ filename ^ "' does not have " ^ ext ^ " extension!\n");;

let file (ext : string) =
  C.Command.Arg_type.create
    (fun filename ->
      match C.Sys.is_file filename with
          `No | `Unknown ->
            begin
              EM.error EM.File None ("'" ^ filename ^ "' is not a regular file!\n")
            end
        | `Yes -> check_extension filename ext)

let frac_file = file ".frac"

let frac_command =
  C.Command.basic
    ~summary:"Typechecking FracST files"
    C.Command.Let_syntax.(
      let%map_open
        verbosity = flag "-v" (optional_with_default 0 int)
          ~doc:"verbosity:- 0: quiet, 1: default, 2: verbose, 3: debugging mode"
        (* and syntax = flag "-s" (optional_with_default "explicit" string)
             ~doc:"syntax: implicit, explicit" *)
        (* and tc_only = flag "-tc" no_arg
             ~doc:"type check only" *)
        (* and run_only = flag "-run" no_arg
             ~doc:"check and run non-blockchain program" *)
        and file = anon("filename" %: frac_file) in
        fun () ->
          let rawtxn = TL.read file in
          (* let TL.RawTransaction env = rawtxn in
             let () = print_endline (PP.pp_prog env) in *)
          F.verbosity := verbosity;
          let _txn = TL.check rawtxn in
          ())

let () =
  C.Command.run ~version:"1.0" ~build_info:"stable" frac_command;;
