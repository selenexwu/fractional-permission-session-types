open Sexplib.Std
module R = Arith

type ext = Mark.ext option      (* optional extent (source region info) *)

let make_ext (startpos : Lexing.position) (endpos : Lexing.position): ext =
  Some(((startpos.Lexing.pos_lnum, startpos.Lexing.pos_cnum - startpos.Lexing.pos_bol + 1),
        (endpos.Lexing.pos_lnum, endpos.Lexing.pos_cnum - endpos.Lexing.pos_bol + 1),
        startpos.Lexing.pos_fname))

(* Session Types *)
type label = string (* l,k for internal and external choice *)
type tpname = string            (* v, for types defined with v = A *)
type expname = string  (* f, for processes defined with f = P *)
type permname = string (* p, for permissions *)
type idname = string (* a, b, for identifiers *)

module StringMap = Map.Make(String)

(* Permissions *)
type perm =
  | Owned
  | Fractional of float StringMap.t

let perm_is_simple p =
  match p with
  | Owned -> true
  | Fractional pm -> StringMap.cardinal pm = 1 && StringMap.mem "" pm

exception NonlinearPerm

let perm_mult p1 p2 =
  match p1, p2 with
  | Owned, _ -> Owned
  | _, Owned -> p1
  | Fractional p1, Fractional p2 ->
    if perm_is_simple (Fractional p1) then
      let p1 = StringMap.find "" p1 in
      Fractional (StringMap.map (fun x -> x *. p1) p2)
    else if perm_is_simple (Fractional p2) then
      let p2 = StringMap.find "" p2 in
      Fractional (StringMap.map (fun x -> x *. p2) p1)
    else raise NonlinearPerm

let perm_add p1 p2 =
  match p1, p2 with
  | Owned, _ | _, Owned -> Owned
  | Fractional p1, Fractional p2 ->
    Fractional (StringMap.union (fun _v x1 x2 -> Some (x1 +. x2)) p1 p2)


type chan = string       (* channel name *)
[@@deriving sexp]

type stype = proto * perm * idname
and proto =
    Plus of choices                   (* +{...} *)
  | With of choices                   (* &{...} *)
  | Tensor of stype * proto           (* A * B *)
  | Lolli of stype * proto            (* A -o B *)
  | One                               (* 1 *)
  | TpName of tpname                  (* v *)
  | Up of proto                       (* /\ A *)
  | Down of proto                     (* \/ A *)
  | DoubleDown of proto               (* \\// A *)
  | ExistsId of idname * proto        (* ?a. A *)
  | ForallId of idname * proto        (* !a. A *)
  | ExistsPerm of permname * proto    (* ??a. A *)
  | ForallPerm of permname * proto    (* !!a. A *)

and choices = (label * proto) list

and 'a st_aug_expr =
{
  st_structure : 'a st_expr;
  st_data : 'a;
}
and 'a st_expr =
  (* judgmental constructs *)
  | Fwd of chan * chan                                      (* x <- y *)
  | Spawn of idname * chan * expname *
             idname list * permname list * chan list *
             'a st_aug_expr                                 (* {a}, x <- f[a][p] <- [y] ; Q *)
  | ExpName of chan * expname * idname list *
               permname list * chan list                    (* x <- f <- [y] *)

  (* choice +{...} or &{...} *)
  | Lab of chan * label * 'a st_aug_expr                    (* x.k ; P *)
  | Case of chan * 'a branches                              (* case x (...) *)

  (* tensor or lolli *)
  | Send of chan * chan * 'a st_aug_expr                    (* send x w ; P *)
  | Recv of chan * chan * 'a st_aug_expr                    (* y <- recv x ; P *)

  (* termination 1 *)
  | Close of chan                                           (* close x *)
  | Wait of chan * 'a st_aug_expr                           (* wait x ; P *)

  (* mutability /\ \/ \\// *)
  | Immut of chan list * 'a st_aug_expr                     (* immut [y] { P } *)
  | Continue of chan list                                   (* continue [y] *)
  | Mut of 'a st_aug_expr                                   (* mut { P } *)
  | Start of chan * 'a st_aug_expr                          (* start x ; P *)
  | Finish of chan * 'a st_aug_expr                         (* finish x ; P *)
  | Mutate of chan * 'a st_aug_expr                         (* mutate x ; P *)

  (* permission management *)
  | Split of chan * chan * chan * 'a st_aug_expr            (* x1, x2 <- split x ; P *)
  | Merge of chan * chan * chan * 'a st_aug_expr            (* x <- merge x1, x2 ; P *)
  | Share of chan * 'a st_aug_expr                          (* share x ; P *)
  | Own of chan * 'a st_aug_expr                            (* own x ; P *)

  (* exists ?a. ??a. and forall !a. !!a. *)
  | SendId of chan * idname * 'a st_aug_expr                (* send x {a} ; P *)
  | RecvId of chan * idname * 'a st_aug_expr                (* {b} <- recv x ; P *)
  | SendPerm of chan * perm * 'a st_aug_expr                (* send x {{a}} ; P *)
  | RecvPerm of chan * permname * 'a st_aug_expr            (* {{a}} <- recv x ; P *)

  (* Nomos specific, get channel from id *)
  | Abort                                                       (* abort *)
  | Print of printable list * chan list * 'a st_aug_expr

and printable = 
    Word of string
  | PInt 
  | PBool 
  | PStr 
  | PAddr 
  | PChan
  | PNewline

and 'a branch = label * 'a st_aug_expr

and 'a branches = 'a branch list                          (* (l1 => P1 | ... | ln => Pn) *)

type parsed_expr = ext st_aug_expr

type typed_expr = stype st_aug_expr

type chan_tp = chan * stype

type label_proto = chan * proto

type context =
  {
    idnames: idname list;
    permnames: permname list;
    owned: idname list;
    locked: chan_tp list;
    linear: chan_tp list;
  }

type decl =
  | TpDef of tpname * proto                         (* type a = A *)
  | ExpDecDef of expname *
                 (idname list * permname list *
                  chan_tp list * label_proto) *         (* proc f[a][p] : Delta |- c : C = expression *)
                 parsed_expr
  | Exec of expname * chan list                     (* exec f x1 x2 ... *)


type program = (decl * ext) list

type file = (string list * program) (* imports plus the actual program *)

(* Environments *)

exception AstImpossible
exception UndeclaredTp;;

let rec lookup_tp decls v = match decls with
    (TpDef(v',a), _)::decls' ->
      if v = v' then Some a else lookup_tp decls' v
  | (_decl, _)::decls' -> lookup_tp decls' v
  | [] -> None;;

let expd_tp env v = match lookup_tp env v with
    Some a -> a
  | None -> raise UndeclaredTp;;

let rec lookup_expdec decls f = match decls with
    (ExpDecDef(f',(ids, perms, ctx, zc),_p), _)::decls' ->
      if f = f' then Some (ids,perms,ctx,zc) else lookup_expdec decls' f
  | _decl::decls' -> lookup_expdec decls' f
  | [] -> None;;

let rec lookup_expdef decls f = match decls with
    (ExpDecDef(f',_dec,p), _)::decls' ->
      if f = f' then Some p else lookup_expdef decls' f
  | _decl::decls' -> lookup_expdef decls' f
  | [] -> None;;

let rec lookup_choice cs k = match cs with
    (l,a)::choices' ->
      if k = l then Some a
      else lookup_choice choices' k
  | [] -> None;;

(*************************)
(* Operational Semantics *)
(*************************)

let sub c' c x =
  if x = c then c' else x

let sub_arg c' c a = match a with
  | x -> (sub c' c x);;

let eq_name c1 c2 = (c1 = c2)

let subst_list c' c l = List.map (fun a -> sub_arg c' c a) l;; 

let rec subst c' c expr = match expr with
    Fwd(x,y) -> Fwd(sub c' c x, sub c' c y)
  | Spawn(a,x,f,ids,ps,xs,q) ->
      if eq_name c x
      then Spawn(a,x,f,ids,ps, subst_list c' c xs, q)
      else Spawn(a,x,f,ids,ps, subst_list c' c xs, subst_aug c' c q)
  | ExpName(x,f,ids,ps,xs) -> ExpName(x,f,ids,ps, subst_list c' c xs)
  | Lab(x,k,p) -> Lab(sub c' c x, k, subst_aug c' c p)
  | Case(x,branches) -> Case(sub c' c x, subst_branches c' c branches)
  | Send(x,w,p) -> Send(sub c' c x, sub c' c w, subst_aug c' c p)
  | Recv(x,y,p) ->
      if eq_name c y
      then Recv(sub c' c x, y, p)
      else Recv(sub c' c x, y, subst_aug c' c p)
  | Close(x) -> Close(sub c' c x)
  | Wait(x,q) -> Wait(sub c' c x, subst_aug c' c q)
  | Abort -> Abort
  | Print(l,args,p) -> Print(l, subst_list c' c args, subst_aug c' c p)

and subst_branches c' c bs = match bs with
    [] -> []
  | (l,p)::bs' ->
      (l, subst_aug c' c p)::(subst_branches c' c bs')

and subst_aug c' c {st_structure = exp; st_data = d} =
  {st_structure = subst c' c exp; st_data = d}

exception SplitError

let split_last l =
  if List.length l <= 1
  then raise SplitError
  else
    let revl = List.rev l in
    match revl with
        [] -> raise AstImpossible
      | e::es -> (List.rev es, e);;
