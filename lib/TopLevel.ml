module A = Ast
module C = Core
module Map = C.Map
module Sexp = C.Sexp
module TC = Typecheck
module StdList = Stdlib.List
module LEX = Lexer
module L = Lexing
module EM = ErrorMsg

type environment = (A.decl * A.ext) list

(*********************************)
(* Loading and Elaborating Files *)
(*********************************)

let init (lexbuf : Lexing.lexbuf) (fname : string) : unit =
  lexbuf.lex_curr_p <- {pos_fname= fname; pos_lnum= 1; pos_bol= 0; pos_cnum= 0}

let ereset () = ErrorMsg.reset ()

let print_position lexbuf =
  let pos = lexbuf.L.lex_curr_p in
  pos.L.pos_fname ^ ":"
  ^ string_of_int pos.L.pos_lnum
  ^ ":"
  ^ string_of_int (pos.L.pos_cnum - pos.L.pos_bol + 1)

(* lex and parse using Menhir, then return list of declarations *)
let parse_with_error lexbuf =
  try Parser.file Lexer.token lexbuf with
  | LEX.SyntaxError msg ->
      let lex_error =
        "Lexing Failure: " ^ print_position lexbuf ^ ": " ^ msg ^ "\n"
      in
      raise (EM.LexError lex_error)
  | Parser.Error ->
      let parse_error = "Parsing Failure: " ^ print_position lexbuf ^ "\n" in
      raise (EM.ParseError parse_error)

(* try to read a file, or print failure *)
let read_with_error file =
  try C.In_channel.read_all file
  with Sys_error msg ->
    let errormsg = "Failed to load file:\n- " ^ msg ^ "\n" in
    raise (EM.FileError errormsg)

(* open file and parse into environment *)
let read file =
  let rec read_env file =
    let () = ereset () in
    (* internal lexer and parser state *)
    let inx = read_with_error file in
    (* read file *)
    let lexbuf = Lexing.from_string inx in
    (* lex file *)
    let () = init lexbuf file in
    let imports, env = parse_with_error lexbuf in
    (* parse file *)
    let imports' = List.map (Filename.concat (Filename.dirname file)) imports in
    let envs = List.map read_env imports' in
    (List.concat (envs @ [env]) : environment)
  in
  read_env file

let check decls =
  let () = TC.check_redecl decls in
  let () = TC.check_valid decls decls in
  let () = TC.check_decls decls decls in
  ()
