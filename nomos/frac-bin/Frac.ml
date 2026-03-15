(* module NC = Lib.NomosConfig *)
module C = Core
module TL = Lib_frac.TopLevel
module PP = Lib_frac.Pprint
module F = Lib_frac.FracFlags

(* let () =
     C.Command.run ~version:"1.0" ~build_info:"stable" NC.nomos_command;; *)

let () =
  let file = "frac-tests/roundtrip.frac" in
  let rawtxn = TL.read file in
  let TL.RawTransaction env = rawtxn in
  let () = print_endline (PP.pp_prog env) in
  F.verbosity := 2;
  let _txn = TL.check rawtxn in
  ()
