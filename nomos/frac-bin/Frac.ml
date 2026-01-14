(* module NC = Lib.NomosConfig *)
module C = Core
module TL = Lib_frac.TopLevel
module PP = Lib_frac.Pprint

(* let () =
     C.Command.run ~version:"1.0" ~build_info:"stable" NC.nomos_command;; *)

let () =
  let file = "frac-tests/queue.frac" in
  let TL.RawTransaction rawtxn = TL.read file in
  print_endline (PP.pp_prog rawtxn)
