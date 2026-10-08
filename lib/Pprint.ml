module A = Ast

let pp_list = String.concat ","

let rec spaces n = if n <= 0 then "" else " " ^ spaces (n - 1)

let len s = String.length s

let pp_perm p =
  match p with
  | A.Owned ->
      "*"
  | A.Fractional pm ->
      String.concat "+"
      @@ List.map (fun (v, x) -> Q.to_string x ^ if v = "" then "" else "*" ^ v)
      @@ A.StringMap.bindings pm

let pp_perms ps = pp_list (List.map pp_perm ps)

let rec pp_tp_simple (a, p, id) =
  "<" ^ pp_proto_simple a ^ "," ^ pp_perm p ^ "," ^ id ^ ">"

and pp_proto_simple a =
  match a with
  | A.One ->
      "1"
  | A.Plus choice ->
      "+{ " ^ pp_choice_simple choice ^ " }"
  | A.With choice ->
      "&{ " ^ pp_choice_simple choice ^ " }"
  | A.Tensor (a, b) ->
      pp_tp_simple a ^ " * " ^ pp_proto_simple b
  | A.Lolli (a, b) ->
      pp_tp_simple a ^ " -o " ^ pp_proto_simple b
  | A.Up (k, a) ->
      "/\\ " ^ k ^ "." ^ pp_proto_simple a
  | A.Down a ->
      "\\/ " ^ pp_proto_simple a
  | A.DoubleDown a ->
      "\\\\//" ^ pp_proto_simple a
  | A.ExistsId (a, t) ->
      "?" ^ a ^ "." ^ pp_proto_simple t
  | A.ForallId (a, t) ->
      "!" ^ a ^ "." ^ pp_proto_simple t
  | A.ExistsPerm (a, t) ->
      "??" ^ a ^ "." ^ pp_proto_simple t
  | A.ForallPerm (a, t) ->
      "!!" ^ a ^ "." ^ pp_proto_simple t
  | A.TpName a ->
      a

and pp_choice_simple cs =
  match cs with
  | [] ->
      ""
  | [(l, a)] ->
      l ^ " : " ^ pp_proto_simple a
  | (l, a) :: cs' ->
      l ^ " : " ^ pp_proto_simple a ^ ", " ^ pp_choice_simple cs'

let pp_label_proto (c, a) = "(" ^ c ^ " : " ^ pp_proto_simple a ^ ")"

let pp_channames chans = String.concat " " chans

(* pp_proto i A = "A", where i is the indentation after a newline
 *)
let rec pp_proto i a =
  match a with
  | A.Plus choice ->
      "+{ " ^ pp_choice (i + 3) choice ^ " }"
  | A.With choice ->
      "&{ " ^ pp_choice (i + 3) choice ^ " }"
  | A.Tensor (a, b) ->
      let astr = pp_tp_simple a in
      let inc = len astr in
      astr ^ " * " ^ pp_proto (i + inc) b
  | A.Lolli (a, b) ->
      let astr = pp_tp_simple a in
      let inc = len astr in
      astr ^ " -o " ^ pp_proto (i + inc) b
  | A.One ->
      "1"
  | A.Up (k, a) ->
      let inc = len k + 4 in
      "/\\" ^ k ^ ". " ^ pp_proto (i + inc) a
  | A.Down a ->
      "\\/ " ^ pp_proto (i + 3) a
  | A.DoubleDown a ->
      "\\\\// " ^ pp_proto (i + 5) a
  | A.ExistsId (a, t) ->
      let inc = len a + 3 in
      "?" ^ a ^ ". " ^ pp_proto (i + inc) t
  | A.ForallId (a, t) ->
      let inc = len a + 3 in
      "!" ^ a ^ ". " ^ pp_proto (i + inc) t
  | A.ExistsPerm (a, t) ->
      let inc = len a + 4 in
      "??" ^ a ^ ". " ^ pp_proto (i + inc) t
  | A.ForallPerm (a, t) ->
      let inc = len a + 4 in
      "!!" ^ a ^ ". " ^ pp_proto (i + inc) t
  | A.TpName v ->
      v

and pp_tp_after i s a = s ^ pp_proto (i + len s) a

and pp_choice i cs =
  match cs with
  | [] ->
      ""
  | [(l, a)] ->
      pp_tp_after i (l ^ " : ") a
  | (l, a) :: cs' ->
      pp_tp_after i (l ^ " : ") a ^ ",\n" ^ pp_choice_indent i cs'

and pp_choice_indent i cs = spaces i ^ pp_choice i cs

let pp_proto = fun _env -> fun a -> pp_proto 0 a

let rec pp_lsctx env delta =
  match delta with
  | [] ->
      "."
  | [(x, a)] ->
      "(" ^ x ^ " : " ^ pp_proto_simple a ^ ")"
  | (x, a) :: delta' ->
      "(" ^ x ^ " : " ^ pp_proto_simple a ^ ")" ^ ", "
      ^ pp_lsctx env delta'

let pp_arg (x, a) = "(" ^ x ^ " : " ^ pp_tp_simple a ^ ")"

let rec pp_chantp_list ctx =
  match ctx with
  | [] ->
      "."
  | [xa] ->
      pp_arg xa
  | xa :: ctx' ->
      pp_arg xa ^ ", " ^ pp_chantp_list ctx'

(* pp_tp_compact env delta pot a = "V; O; ldelta; delta |-_N C", on one line *)
let pp_tpj_compact env delta (x, a) =
  pp_channames delta.A.idnames
  ^ ","
  ^ pp_channames delta.A.permnames
  ^ ";"
  ^ pp_chantp_list delta.A.locked
  ^ ";"
  ^ pp_chantp_list delta.A.linear
  ^ " |- (" ^ x ^ " : " ^ pp_proto_simple a ^ ")"

let pp_printable x =
  match x with A.Word s -> s | A.PChan -> "%c" | A.PNewline -> "\\n"

(***********************)
(* Process expressions *)
(***********************)

let rec pp_exp env i exp =
  match exp with
  | A.Fwd (x, y) ->
      x ^ " <-> " ^ y
  | A.Spawn (a, x, f, ids, ps, xs, q) ->
      (* exp = x <- f <- xs ; q *)
      (match a with None -> "" | Some a -> "{" ^ a ^ "}, ")
      ^ x ^ " <- " ^ f ^ "[" ^ pp_list ids ^ "]{" ^ pp_perms ps ^ "} "
      ^ pp_argnames env xs ^ " ;\n" ^ pp_exp_indent env i q
  | A.ExpName (x, f, ids, ps, xs) ->
      x ^ " <- " ^ f ^ "[" ^ pp_list ids ^ "]{" ^ pp_perms ps ^ "} "
      ^ pp_argnames env xs
  | A.Lab (x, k, p) ->
      x ^ "." ^ k ^ " ;\n" ^ pp_exp_indent env i p
  | A.Case (x, bs) ->
      "case " ^ x ^ " ( "
      ^ pp_branches env (i + 8 + len (x)) bs
      ^ " )"
  | A.Send (x, w, p) ->
      "send " ^ x ^ " " ^ w ^ " ;\n" ^ pp_exp_indent env i p
  | A.Recv (x, y, p) ->
      y ^ " <- recv " ^ x ^ " ;\n" ^ pp_exp_indent env i p
  | A.Close x ->
      "close " ^ x
  | A.Wait (x, q) ->
      "wait " ^ x ^ " ;\n" ^ pp_exp_indent env i q
  | A.Immut (xs, perm, p) ->
      "immut " ^ pp_channames xs ^ " { " ^ perm ^ " =>\n"
      ^ pp_exp_indent env (i + 2) p
      ^ "\n" ^ spaces i ^ "}"
  | A.Continue xs ->
      "continue " ^ pp_channames xs
  | A.Mut p ->
      "mut {\n" ^ pp_exp_indent env (i + 2) p ^ "\n" ^ spaces i ^ "}"
  | A.Start (x, perm, p) ->
      "start " ^ x ^ "{" ^ pp_perm perm ^ "} ;\n"
      ^ pp_exp_indent env i p
  | A.Finish (x, p) ->
      "finish " ^ x ^ " ;\n" ^ pp_exp_indent env i p
  | A.Mutate (x, p) ->
      "mutate " ^ x ^ " ;\n" ^ pp_exp_indent env i p
  | A.Split (x1, x2, x, p) ->
      x1 ^ ", " ^ x2 ^ " <- split " ^ x ^ " ;\n"
      ^ pp_exp_indent env i p
  | A.Merge (x, x1, x2, p) ->
      x ^ " <- merge " ^ x1 ^ ", " ^ x2 ^ " ;\n"
      ^ pp_exp_indent env i p
  | A.Share (x, p) ->
      "share " ^ x ^ " ;\n" ^ pp_exp_indent env i p
  | A.Own (x, p) ->
      "own " ^ x ^ " ;\n" ^ pp_exp_indent env i p
  | A.SendId (x, a, p) ->
      "send " ^ x ^ " {" ^ a ^ "} ;\n" ^ pp_exp_indent env i p
  | A.RecvId (x, a, p) ->
      "{" ^ a ^ "} <- recv " ^ x ^ " ;\n" ^ pp_exp_indent env i p
  | A.SendPerm (x, a, p) ->
      "send " ^ x ^ " {{" ^ pp_perm a ^ "}} ;\n" ^ pp_exp_indent env i p
  | A.RecvPerm (x, a, p) ->
      "{{" ^ a ^ "}} <- recv " ^ x ^ " ;\n" ^ pp_exp_indent env i p
  | A.Abort ->
      "abort"
  | A.Print (l, args, p) ->
      "print(" ^ pp_printable_list env l args ^ ");\n" ^ pp_exp_indent env i p

and pp_printable_list env l args =
  let s1 = List.map pp_printable l in
  let s1' = List.fold_left (fun x y -> x ^ y) "\"" s1 in
  let s2 = pp_argnames env args in
  match args with [] -> s1' ^ "\"" | _ -> s1' ^ "\", " ^ s2

and pp_exp_indent env i p = spaces i ^ pp_exp env i p.A.st_structure

and pp_exp_after env i s p = s ^ pp_exp env (i + len s) p

and pp_branches env i bs =
  match bs with
  | [] ->
      ""
  | [(l, p)] ->
      pp_exp_after env i (l ^ " => ") p.A.st_structure
  | (l, p) :: bs' ->
      pp_exp_after env i (l ^ " => ") p.A.st_structure
      ^ "\n"
      ^ pp_branches_indent env i bs'

and pp_branches_indent env i bs = spaces (i - 2) ^ "| " ^ pp_branches env i bs

and pp_argnames env args =
  match args with
  | [] ->
      ""
  | [a] ->
     a
  | a :: args' ->
      a ^ " " ^ pp_argnames env args'

let pp_exp_prefix exp =
  match exp with
  | A.Fwd (x, y) ->
      x ^ " <-> " ^ y
  | A.Spawn (a, x, f, ids, ps, xs, _q) ->
      (* exp = x <- f <- xs ; q *)
      (match a with None -> "" | Some a -> "{" ^ a ^ "}, ")
      ^ x ^ " <- " ^ f ^ "[" ^ pp_list ids ^ "][" ^ pp_perms ps
      ^ "] <- " ^ pp_argnames () xs ^ " ; ..."
  | A.ExpName (x, f, ids, ps, xs) ->
      x ^ " <- " ^ f ^ "[" ^ pp_list ids ^ "]{" ^ pp_perms ps ^ "} <- "
      ^ pp_argnames () xs
  | A.Lab (x, k, _p) ->
      x ^ "." ^ k ^ " ; ..."
  | A.Case (x, _bs) ->
      "case " ^ x ^ " ( ... )"
  | A.Send (x, w, _p) ->
      "send " ^ x ^ " " ^ w ^ " ; ..."
  | A.Recv (x, y, _p) ->
      y ^ " <- recv " ^ x ^ " ; ..."
  | A.Close x ->
      "close " ^ x
  | A.Wait (x, _q) ->
      "wait " ^ x ^ " ; ..."
  | A.Immut (xs, p, _p) ->
      "immut " ^ pp_channames xs ^ " { " ^ p ^ " => ... }"
  | A.Continue xs ->
      "continue " ^ pp_channames xs
  | A.Mut _p ->
      "mut { ... }"
  | A.Start (x, perm, _p) ->
      "start " ^ x ^ "{" ^ pp_perm perm ^ "} ; ..."
  | A.Finish (x, _p) ->
      "finish " ^ x ^ " ; ..."
  | A.Mutate (x, _p) ->
      "mutate " ^ x ^ " ; ..."
  | A.Split (x1, x2, x, _p) ->
      x1 ^ ", " ^ x2 ^ " <- split " ^ x ^ " ; ..."
  | A.Merge (x, x1, x2, _p) ->
      x ^ " <- merge " ^ x1 ^ ", " ^ x2 ^ " ; ..."
  | A.Share (x, _p) ->
      "share " ^ x ^ " ; ..."
  | A.Own (x, _p) ->
      "own " ^ x ^ " ; ..."
  | A.SendId (x, a, _p) ->
      "send " ^ x ^ " {" ^ a ^ "} ; ..."
  | A.RecvId (x, a, _p) ->
      "{" ^ a ^ "} <- recv " ^ x ^ " ; ..."
  | A.SendPerm (x, a, _p) ->
      "send " ^ x ^ " {{" ^ pp_perm a ^ "}} ; ..."
  | A.RecvPerm (x, a, _p) ->
      "{{" ^ a ^ "}} <- recv " ^ x ^ " ; ..."
  | A.Abort ->
      "abort"
  | A.Print (l, args, _) ->
      "print(" ^ pp_printable_list () l args ^ "); ..."

(****************)
(* Declarations *)
(****************)

let pp_decl env dcl =
  match dcl with
  | A.TpDef (v, a) ->
      pp_tp_after 0 ("type " ^ v ^ " = ") a
  | A.ExpDecDef (f, (ids, ps, delta, (x, a)), p) ->
      "proc " ^ f ^ "[" ^ pp_list ids ^ "]{" ^ pp_list ps ^ "} : "
      ^ pp_chantp_list delta ^ " |- "
      ^ pp_label_proto (x, a)
      ^ " = \n" ^ pp_exp_indent env 2 p

let pp_progh env decls =
  List.fold_left (fun s (d, _ext) -> s ^ pp_decl env d ^ "\n") "" decls

let pp_prog env = pp_progh env env
