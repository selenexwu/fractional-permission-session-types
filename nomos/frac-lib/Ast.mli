module R = Arith
type ext = Mark.ext option
val make_ext : Lexing.position -> Lexing.position -> ext
type label = string
type tpname = string
type expname = string
type permname = string
type idname = string
module StringMap : Map.S with type key = string
type perm =
  | Owned
  | Fractional of float StringMap.t
val perm_is_simple : perm -> bool
exception NonlinearPerm
val perm_mult : perm -> perm -> perm
val perm_add : perm -> perm -> perm
type chan = string
type stype = proto * perm * idname
and proto =
    Plus of choices
  | With of choices
  | Tensor of stype * proto
  | Lolli of stype * proto
  | One
  | TpName of tpname
  | Up of proto
  | Down of proto
  | DoubleDown of proto
  | ExistsId of idname * proto
  | ForallId of idname * proto
  | ExistsPerm of permname * proto
  | ForallPerm of permname * proto
and choices = (label * proto) list
and 'a st_aug_expr = { st_structure : 'a st_expr; st_data : 'a; }
and 'a st_expr =
    Fwd of chan * chan
  | Spawn of idname * chan * expname * idname list * permname list * chan list * 'a st_aug_expr
  | ExpName of chan * expname * idname list * permname list * chan list
  | Lab of chan * label * 'a st_aug_expr
  | Case of chan * 'a branches
  | Send of chan * chan * 'a st_aug_expr
  | Recv of chan * chan * 'a st_aug_expr
  | Close of chan
  | Wait of chan * 'a st_aug_expr
  | Immut of chan list * 'a st_aug_expr
  | Continue of chan list
  | Mut of 'a st_aug_expr
  | Start of chan * 'a st_aug_expr
  | Finish of chan * 'a st_aug_expr
  | Mutate of chan * 'a st_aug_expr
  | Split of chan * chan * chan * 'a st_aug_expr
  | Merge of chan * chan * chan * 'a st_aug_expr
  | Share of chan * 'a st_aug_expr
  | Own of chan * 'a st_aug_expr
  | SendId of chan * idname * 'a st_aug_expr
  | RecvId of chan * idname * 'a st_aug_expr
  | SendPerm of chan * perm * 'a st_aug_expr
  | RecvPerm of chan * permname * 'a st_aug_expr
  | Abort
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
and 'a branches = 'a branch list
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
  | TpDef of tpname * proto
  | ExpDecDef of expname *
                 (idname list * permname list *
                  chan_tp list * label_proto) *
                 parsed_expr
  | Exec of expname * chan list


type program = (decl * ext) list
type file = string list * program
exception UndeclaredTp
val lookup_tp : (decl * 'a) list -> tpname -> proto option
val expd_tp : (decl * 'a) list -> tpname -> proto
val lookup_expdec :
  (decl * 'a) list ->
  expname -> (idname list * permname list * chan_tp list * label_proto) option
val lookup_expdef : (decl * 'a) list -> expname -> parsed_expr option
val lookup_choice : ('a * 'b) list -> 'a -> 'b option
val subst :
  string -> string -> 'a st_expr -> 'a st_expr
val subst_aug :
  string -> string -> 'a st_aug_expr -> 'a st_aug_expr
val split_last : 'a list -> 'a list * 'a
