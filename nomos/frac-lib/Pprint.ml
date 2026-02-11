module R = Arith
module A = Ast

(**************************)
(* Arithmetic expressions *)
(**************************)
              
(* Uses precedence
 * prec('+','-') = 1; prec('*') = 2
 *)
let parens prec_left prec s =
    if prec_left >= prec then "(" ^ s ^ ")" else s;;

(* pp_arith_prec prec_left e = "e"
 * using the precedence prec_left of the operator
 * to the left to decide on parentheses
 * All arithmetic operators are left associative
 *)
let rec pp_arith_prec prec_left e = match e with
    R.Int(n) ->
      if n >= 0 then string_of_int n
      else pp_arith_prec prec_left (R.Sub(R.Int(0),R.Int(0-n))) (* might overflow *)
  | R.Add(s,t) ->
      parens prec_left 1 (pp_arith_prec 0 s ^ "+" ^ pp_arith_prec 1 t)
  | R.Sub(s,t) ->
      parens prec_left 1 (pp_arith_prec 0 s ^ "-" ^ pp_arith_prec 1 t)
  | R.Mult(s,t) ->
    parens prec_left 2 (pp_arith_prec 1 s ^ "*" ^ pp_arith_prec 2 t)
  | R.Var(v) -> v;;

(* pp_arith e = "e" *)
let pp_arith e = pp_arith_prec 0 e;;

(*******************************)
(* Types, and their components *)
(*******************************)

(***********************)
(* Externalizing types *)
(***********************)

(*******************************)
(* Multiline Printing of Types *)
(*******************************)

let rec spaces n =
    if n <= 0 then ""
    else " " ^ spaces (n-1);;

let len s = String.length s;;

let pp_perm p = match p with
  | A.Owned -> "*"
  | A.Fraction(f) -> string_of_float f
  | A.VarPerm(p) -> p

let rec pp_tp_simple (a,p,id) =
  "<" ^ pp_proto_simple a ^ "," ^ pp_perm p ^ "," ^ id ^ ">"
and pp_proto_simple a = match a with
    A.One -> "1"
  | A.Plus(choice) -> "+{ " ^ pp_choice_simple choice ^ " }"
  | A.With(choice) -> "&{ " ^ pp_choice_simple choice ^ " }"
  | A.Tensor(a,b) -> pp_tp_simple a ^ " * " ^ pp_proto_simple b
  | A.Lolli(a,b) -> pp_tp_simple a ^ " -o " ^ pp_proto_simple b
  | A.Up(a) -> "/\\ " ^ pp_proto_simple a
  | A.Down(a) -> "\\/ " ^ pp_proto_simple a
  | A.TpName(a) -> a

and pp_choice_simple cs = match cs with
    [] -> ""
  | [(l,a)] -> l ^ " : " ^ pp_proto_simple a
  | (l,a)::cs' ->
      l ^ " : " ^ pp_proto_simple a ^ ", " ^ pp_choice_simple cs';;

let pp_chan (c) = c

let pp_label_proto (c,a) = "(" ^ pp_chan c ^ " : " ^ pp_proto_simple a ^ ")";;

let rec pp_channames chans = match chans with
    [] -> ""
  | [c] -> pp_chan c
  | c::chans' -> pp_chan c ^ " " ^ pp_channames chans';;

(* pp_proto i A = "A", where i is the indentation after a newline
 * A must be externalized, or internal name '%n' will be printed
 *)
let rec pp_proto i a = match a with
    A.Plus(choice) -> "+{ " ^ pp_choice (i+3) choice ^ " }"
  | A.With(choice) -> "&{ " ^ pp_choice (i+3) choice ^ " }"
  | A.Tensor(a,b) ->
      (* TODO: don't use simple here *)
      let astr = pp_tp_simple a in
      let inc = len astr in
      astr ^ " * " ^ pp_proto (i+inc) b
  | A.Lolli(a,b) ->
      (* TODO: don't use simple here *)
      let astr = pp_tp_simple a in
      let inc = len astr in
      astr ^ " -o " ^ pp_proto (i+inc) b
  | A.One -> "1"
  | A.Up(a) ->
      "/\\ " ^ pp_proto (i+3) a
  | A.Down(a) ->
      "\\/ " ^ pp_proto (i+3) a
  | A.DoubleDown(a) ->
      "\\\\// " ^ pp_proto (i+5) a
  | A.ExistsId(a,t) ->
      let inc = (len a) + 3 in
      "?" ^ a ^ ". " ^ pp_proto (i+inc) t
  | A.ForallId(a,t) ->
      let inc = (len a) + 3 in
      "!" ^ a ^ ". " ^ pp_proto (i+inc) t
  | A.ExistsPerm(a,t) ->
      let inc = (len a) + 4 in
      "??" ^ a ^ ". " ^ pp_proto (i+inc) t
  | A.ForallPerm(a,t) ->
      let inc = (len a) + 4 in
      "!!" ^ a ^ ". " ^ pp_proto (i+inc) t
  | A.TpName(v) -> v

and pp_tp_after i s a = s ^ pp_proto (i+len(s)) a

and pp_choice i cs = match cs with
    [] -> ""
  | [(l,a)] ->
    pp_tp_after i (l ^ " : ") a
  | (l,a)::cs' ->
    pp_tp_after i (l ^ " : ") a ^ ",\n"
    ^ pp_choice_indent i cs'
and pp_choice_indent i cs = spaces i ^ pp_choice i cs;;

let pp_proto = fun _env -> fun a -> pp_proto 0 a;;

let rec pp_lsctx env delta = match delta with
    [] -> "."
  | [(x,a)] -> "(" ^ pp_chan x ^ " : " ^ pp_proto_simple a ^ ")"
  | (x,a)::delta' -> "(" ^ pp_chan x ^ " : " ^ pp_proto_simple a ^ ")" ^ ", " ^ pp_lsctx env delta';;

let pp_arg (x,a) = "(" ^ pp_chan x ^ " : " ^ pp_tp_simple a ^ ")"

let rec pp_chantp_list ctx = match ctx with
    [] -> "."
  | [xa] -> pp_arg xa
  | xa::ctx' -> pp_arg xa ^ ", " ^ pp_chantp_list ctx';;

(* pp_tp_compact env delta pot a = "V; O; ldelta; delta |-_N C", on one line *)
let pp_tpj_compact env delta (x,a) =
  pp_channames delta.A.idnames ^ "," ^
  pp_channames delta.A.permnames ^ ";" ^
  pp_chantp_list delta.A.locked ^ ";" ^
  pp_chantp_list delta.A.linear ^ " |- (" ^
  pp_chan x ^ " : " ^ pp_proto_simple a ^ ")";;

let pp_printable x = 
  match x with
      A.Word(s) -> s 
    | A.PInt ->  "%d"
    | A.PBool -> "%b"
    | A.PStr ->  "%s"
    | A.PAddr -> "%a"
    | A.PChan -> "%c"
    | A.PNewline -> "\\n";;

(***********************)
(* Process expressions *)
(***********************)

(* Cut is right associative, so we need paren around
 * the left-hand side of a cut if it is not atomic.
 * Atomic are Id, Case<dir>, CloseR, ExpName
 * Rather than propagating a binding strength downward,
 * we just peek ahead.
 *)

let rec pp_exp env i exp = match exp with
    A.Fwd(x,y) -> pp_chan x ^ " <- " ^ pp_chan y
  | A.Spawn(a,x,f,ids,ps,xs,q) -> (* exp = x <- f <- xs ; q *)
      "{" ^ a ^ "}, " ^ pp_chan x ^ " <- " ^ f ^ "[" ^ pp_channames ids ^ "]{" ^ pp_channames ps ^ "} " ^ pp_argnames env xs ^ " ;\n"
      ^ pp_exp_indent env i q
  | A.ExpName(x,f,ids,ps,xs) -> pp_chan x ^ " <- " ^ f ^ "[" ^ pp_channames ids ^ "]{" ^ pp_channames ps ^ "} " ^ pp_argnames env xs
  | A.Lab(x,k,p) -> pp_chan x ^ "." ^ k ^ " ;\n" ^ pp_exp_indent env i p
  | A.Case(x,bs) -> "case " ^ pp_chan x ^ " ( " ^ pp_branches env (i+8+len (pp_chan x)) bs ^ " )"
  | A.Send(x,w,p) -> "send " ^ pp_chan x ^ " " ^ pp_chan w ^ " ;\n" ^ pp_exp_indent env i p
  | A.Recv(x,y,p) -> pp_chan y ^ " <- recv " ^ pp_chan x ^ " ;\n" ^ pp_exp_indent env i p
  | A.Close(x) -> "close " ^ pp_chan x
  | A.Wait(x,q) -> "wait " ^ pp_chan x ^ " ;\n" ^ pp_exp_indent env i q
  | A.Immut(xs,p) -> "immut " ^ pp_channames xs ^ " {\n" ^ pp_exp_indent env (i+2) p ^ "\n" ^ spaces i ^ "}"
  | A.Continue(xs) -> "continue " ^ pp_channames xs
  | A.Mut(p) -> "mut {\n" ^ pp_exp_indent env (i+2) p ^ "\n" ^ spaces i ^ "}"
  | A.Start(x,p) -> "start " ^ pp_chan x ^ " ;\n" ^ pp_exp_indent env i p
  | A.Finish(x,p) -> "finish " ^ pp_chan x ^ " ;\n" ^ pp_exp_indent env i p
  | A.Mutate(x,p) -> "mutate " ^ pp_chan x ^ " ;\n" ^ pp_exp_indent env i p
  | A.Split(x1,x2,x,p) -> pp_chan x1 ^ ", " ^ pp_chan x2 ^ " <- split " ^ pp_chan x ^ " ;\n" ^ pp_exp_indent env i p
  | A.Merge(x,x1,x2,p) -> pp_chan x ^ " <- merge " ^ pp_chan x1 ^ ", " ^ pp_chan x2 ^ " ;\n" ^ pp_exp_indent env i p
  | A.Share(x,p) -> "share " ^ pp_chan x ^ " ;\n" ^ pp_exp_indent env i p
  | A.Own(x,p) -> "own " ^ pp_chan x ^ " ;\n" ^ pp_exp_indent env i p
  | A.SendId(x,a,p) -> "send " ^ pp_chan x ^ " {" ^ a ^ "} ;\n" ^ pp_exp_indent env i p
  | A.RecvId(x,a,p) -> "{" ^ a ^ "} <- recv " ^ pp_chan x ^ " ;\n" ^ pp_exp_indent env i p
  | A.SendPerm(x,a,p) -> "send " ^ pp_chan x ^ " {{" ^ pp_perm a ^ "}} ;\n" ^ pp_exp_indent env i p
  | A.RecvPerm(x,a,p) -> "{{" ^ a ^ "}} <- recv " ^ pp_chan x ^ " ;\n" ^ pp_exp_indent env i p
  | A.Abort -> "abort"
  | A.Print(l,args,p) -> "print(" ^ pp_printable_list env l args ^ ");\n" ^ pp_exp_indent env i p


and pp_printable_list env l args = 
  let s1 = List.map pp_printable l in
  let s1'  = List.fold_left (fun x y -> x ^ y) "\"" s1 in
  let s2 = pp_argnames env args in
  match args with
      [] -> s1' ^ "\""
    | _ -> s1' ^ "\", " ^ s2

and pp_exp_indent env i p = spaces i ^ pp_exp env i p.A.st_structure
and pp_exp_after env i s p = s ^ pp_exp env (i+len(s)) p

and pp_branches env i bs = match bs with
    [] -> ""
  | [(l,p)] ->
      pp_exp_after env i (l ^ " => ") p.A.st_structure
  | (l,p)::bs' ->
      pp_exp_after env i (l ^ " => ") p.A.st_structure ^ "\n"
      ^ pp_branches_indent env i bs'

and pp_branches_indent env i bs = spaces (i-2) ^ "| " ^ pp_branches env i bs

and pp_argname env arg = match arg with
  | c -> pp_chan c

and pp_argnames env args = match args with
    [] -> ""
  | [a] -> pp_argname env a
  | a::args' -> pp_argname env a ^ " " ^ pp_argnames env args';;

let pp_exp_prefix exp = match exp with
    A.Fwd(x,y) -> pp_chan x ^ " <- " ^ pp_chan y
  | A.Spawn(a,x,f,ids,ps,xs,_q) -> (* exp = x <- f <- xs ; q *)
      "{" ^ a ^ "}, " ^ pp_chan x ^ " <- " ^ f ^ "[" ^ pp_channames ids ^ "][" ^ pp_channames ps ^ "] <- " ^ pp_argnames () xs ^ " ; ..."
  | A.ExpName(x,f,ids,ps,xs) -> pp_chan x ^ " <- " ^ f ^ "[" ^ pp_channames ids ^ "]{" ^ pp_channames ps ^ "} <- " ^ pp_argnames () xs
  | A.Lab(x,k,_p) -> pp_chan x ^ "." ^ k ^ " ; ..."
  | A.Case(x,_bs) -> "case " ^ pp_chan x ^ " ( ... )"
  | A.Send(x,w,_p) -> "send " ^ pp_chan x ^ " " ^ pp_chan w ^ " ; ..."
  | A.Recv(x,y,_p) -> pp_chan y ^ " <- recv " ^ pp_chan x ^ " ; ..."
  | A.Close(x) -> "close " ^ pp_chan x
  | A.Wait(x,_q) -> "wait " ^ pp_chan x ^ " ; ..."
  | A.Abort -> "abort"
  | A.Print(l,args,_) -> "print(" ^ pp_printable_list () l args ^ "); ..."

(****************)
(* Declarations *)
(****************)

let pp_decl env dcl = match dcl with
    A.TpDef(v,a) ->
      pp_tp_after 0 ("type " ^ v ^ " = ") a
  | A.ExpDecDef(f,(ids,ps,delta,(x,a)),p) ->
    "proc " ^ f ^ "[" ^ pp_channames ids ^ "]{" ^ pp_channames ps ^ "} : " ^ pp_chantp_list delta ^ " |- "
    ^ pp_label_proto (x,a) ^ " = \n" ^
    (pp_exp_indent env 2 p)
  | A.Exec(f, l) -> "exec " ^ f ^ " " ^ pp_argnames env l;;

let pp_progh env decls = List.fold_left (fun s (d, _ext) -> s ^ pp_decl env d ^ "\n") "" decls;;

let pp_prog env = pp_progh env env;;
