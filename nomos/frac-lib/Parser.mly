(* import *)
%token <string> IMPORT
(* functional layer *)
%token <int> INT
%token <float> FLOAT
%token <string> ID
%token <Ast.printable list> QUOTED_STRING
%token INTEGER BOOLEAN ADDRESS LIST
%token LPAREN RPAREN
%token TRUE FALSE
%token IF THEN ELSE
%token LET IN
%token EMPTYLIST LSQUARE RSQUARE CONS COMMA
%token EQUALS
%token MATCH WITH BAR 
%token FUN RIGHTARROW
%token PLUS MINUS TIMES DIV
%token EOF
%token NEQ GREATER LESS GREATEREQ LESSEQ
%token ANDALSO ORELSE
%token TYPE PROC ASSET CONTRACT TRANSACTION TURNSTILE EXEC COLON
(* printing *)
%token PRINT
(* Nomos specific *)
%token GETTXNNUM GETTXNSENDER
(* session type layer *)
%token LOLLI AMPERSAND UP DOWN DOUBLEDOWN QUESTION BANG LANGLE RANGLE PRODUCT COIN
%token LBRACE RBRACE
%token HASH DOLLAR
%token FORWARD LARROW SEMI RRARROW
%token RECV SEND CASE DOT CLOSE WAIT WORK DEPOSIT PAY GET ACQUIRE ACCEPT RELEASE DETACH ABORT
%token IMMUT CONTINUE MUT START FINISH MUTATE SPLIT MERGE SHARE OWN
%token MAP INSERT DELETE SIZE NEW
%right ANDALSO ORELSE
%left EQUALS NEQ GREATER LESS GREATEREQ LESSEQ
%right CONS
%left PLUS MINUS
%left TIMES DIV
%nonassoc statement
%start <Ast.file> file
%%


file :
  | imports = list(import); vl = list(decl) EOF { (imports, vl) }
     ;

import :
  | p = IMPORT { p }

mode :
    | ASSET         { Ast.Pure }
    | CONTRACT      { Ast.Shared }
    | TRANSACTION   { Ast.Transaction }
    ;

context_opt :
    | DOT                                   { [] }
    | l = separated_list(COMMA, argument)   { l }
    ;

label_proto :
    | l = ID; COLON; t = proto         { (l,t) }
    ;

sp_proto:
    | x = ID                    { Ast.TpName(x) }
    | INT                       { Ast.One }
    | LPAREN; s = proto; RPAREN { s             }
    | COIN                      { Ast.Coin }
    | MAP; LESS; kt = ftype; COMMA; vt = ftype; GREATER                         { Ast.FMap(kt,vt) }
    | MAP; LESS; kt = ftype; COMMA; vt = proto; GREATER                         { Ast.STMap(kt,vt) }


    ;

sp_ftype:
    | INTEGER                       { Ast.Integer }
    | BOOLEAN                       { Ast.Boolean }
    | ADDRESS                       { Ast.Address }
    | LPAREN; f = ftype; RPAREN     { f }
    ;

perm:
    | TIMES;     { Ast.Owned }
    | p = FLOAT; { Ast.Fraction(p) }
    | p = ID;    { Ast.VarPerm(p) }

stype:
    | LANGLE; t = proto; COMMA; p = perm; COMMA; a = ID; RANGLE { (t,p,a) }
    ;

proto:
    | PLUS; LBRACE; choices = separated_list(COMMA, label_proto); RBRACE        { Ast.Plus(choices) }
    | AMPERSAND; LBRACE; choices = separated_list(COMMA, label_proto); RBRACE   { Ast.With(choices) }
    | s = stype; TIMES; t = proto                                               { Ast.Tensor(s,t) }
    | s = stype; LOLLI; t = proto                                               { Ast.Lolli(s,t) }
    | INT                                                                       { Ast.One }
    | BAR; pot = potential; GREATER; t = proto                                  { Ast.PayPot(pot,t) }
    | LESS; pot = potential; BAR; t = proto                                     { Ast.GetPot(pot,t) }
    | UP; t = proto                                                             { Ast.Up(t) }
    | DOWN; t = proto                                                           { Ast.Down(t) }
    | DOUBLEDOWN; t = proto                                                     { Ast.DoubleDown(t) }
    | QUESTION; a = ID; DOT; t = proto                                          { Ast.ExistsId(a,t) }
    | BANG; a = ID; DOT; t = proto                                              { Ast.ForallId(a,t) }
    | QUESTION; QUESTION; a = ID; DOT; t = proto                                { Ast.ExistsPerm(a,t) }
    | BANG; BANG; a = ID; DOT; t = proto                                        { Ast.ForallPerm(a,t) }
    | a = sp_ftype; RIGHTARROW; t = proto                                       { Ast.FArrow(a,t) }
    | a = sp_ftype; PRODUCT; t = proto                                          { Ast.FProduct(a,t) }
    | COIN                                                                      { Ast.Coin }
    | x = ID                                                                    { Ast.TpName(x) }
    | LPAREN; s = proto; RPAREN                                                 { s }
    | MAP; LESS; kt = ftype; COMMA; vt = ftype; GREATER                         { Ast.FMap(kt,vt) }
    | MAP; LESS; kt = ftype; COMMA; vt = proto; GREATER                         { Ast.STMap(kt,vt) }
    ;

ftype :
    | INTEGER                                               { Ast.Integer }
    | BOOLEAN                                               { Ast.Boolean }
    | ADDRESS                                               { Ast.Address }
    | a = sp_ftype; LIST; pot = potential                   { Ast.ListTP(a,pot) }
    | a = sp_ftype; RIGHTARROW; b = ftype                   { Ast.Arrow(a,b) }
    | LPAREN; a = ftype; RPAREN                             { a }
    ;

argument :
    | LPAREN; a = ID; COLON; t = proto; RPAREN     { Ast.STyped(a, t) }
    | LPAREN; a = ID; COLON; ft = ftype; RPAREN     { Ast.Functional(a, ft) }
    ;

decl : 
    | TYPE; x = ID; EQUALS; t = proto   { (Ast.TpDef (x,t), Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)) }
    | PROC; m = mode; f = ID; COLON; ctx = context_opt; TURNSTILE; LPAREN; c = ID; COLON; t = proto; RPAREN; EQUALS; e = expr                      { (Ast.ExpDecDef(f, m, ({Ast.shared = []; Ast.linear = []; Ast.ordered = ctx}, Ast.Arith(Arith.Int(0)), (c,t)), e),
                                                                                                                                                      Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                                                                                                                                      ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                                                                                                                                      $startpos.Lexing.pos_fname)) }
    | PROC; m = mode; f = ID; COLON; ctx = context_opt; BAR; pot = potential; MINUS; LPAREN; c = ID; COLON; t = proto; RPAREN; EQUALS; e = expr    { (Ast.ExpDecDef(f, m, ({Ast.shared = []; Ast.linear = []; Ast.ordered = ctx}, pot, (c,t)), e),
                                                                                                                                                      Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                                                                                                                                      ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                                                                                                                                      $startpos.Lexing.pos_fname)) }
    | EXEC; f = ID; l = list(app_arg_shared)     { (Ast.Exec(f,l), Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                        ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                        $startpos.Lexing.pos_fname)) }
    ;

expr :
    | LPAREN MINUS i = INT RPAREN     { {Ast.func_structure = Ast.Int (-i); func_data = 
                                        Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} } 
    | LPAREN e = expr RPAREN          { e }
    | TRUE                            { {func_structure = Ast.Bool(true); func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} } 
    | FALSE                           { {func_structure = Ast.Bool(false); func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} }
    | GETTXNNUM                       { {func_structure = Ast.GetTxnNum; func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} }
    | GETTXNSENDER                    { {func_structure = Ast.GetTxnSender; func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} }
    | i = INT                         { {func_structure = Ast.Int(i); func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} } 
    | x = ID                          { {func_structure = Ast.Var(x); func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} } 
    | c = cond                        { {func_structure = c; func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} } 
    | l = letin                       { {func_structure = l; func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} } 
    | lst = listVal                   { {func_structure = lst; func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} } 
    | a = app                         { {func_structure = a; func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} } 
    | c = cons                        { {func_structure = c; func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} } 
    | m = matchExp                    { {func_structure = m; func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} } 
    | l = lambdaExp                   { {func_structure = l; func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} } 
    | o = op                          { {func_structure = o; func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} } 
    | c = compOp                      { {func_structure = c; func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} } 
    | r = relOp                       { {Ast.func_structure = r; Ast.func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} }
    | mp = ID; DOT; SIZE           { {Ast.func_structure = Ast.MapSize(mp); Ast.func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} }
    | LBRACE; s = st; RBRACE          { {func_structure = Ast.Command(s); func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} }
    ;


cond :
    | IF; ifE = expr; THEN; thenE = expr; ELSE; elseE = expr 
                                          {  If (ifE, thenE, elseE) } 
                                          %prec statement
    ;

func :
    | args = id_list; EQUALS; e = expr { {func_structure = Ast.Lambda(args, e); func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} } 
    ;

letin :
    | LET; x = ID; EQUALS; e = expr; IN; inExp = expr { Ast.LetIn (x, e, inExp) } %prec statement
    | LET; FUN; x = ID; f = func; IN; inExp = expr { Ast.LetIn (x, f, inExp) } %prec statement
    ;

listVal : 
      | EMPTYLIST   { Ast.ListE [] }
      | LSQUARE; vl = list_fields; RSQUARE { Ast.ListE vl }
      ;

list_fields :
    | vl = separated_list(SEMI, expr) { vl }
    ;

cons:
    | x = expr; CONS; l = expr { Cons(x, l) }
    ;

op :
   | x = expr; PLUS; y = expr   { Ast.Op(x, Add, y) } 
   | x = expr; TIMES; y = expr  { Ast.Op(x, Mult, y) } 
   | x = expr; MINUS; y = expr  { Ast.Op(x, Sub, y) } 
   | x = expr; DIV; y = expr    { Ast.Op(x, Div, y) } 
   ;


compOp :
   | x = expr; EQUALS; y = expr             { Ast.CompOp(x, Eq, y) }
   | x = expr; EQUALS; EQUALS; y = expr     { Ast.EqAddr(x, y)}
   | x = expr; NEQ; y = expr                { Ast.CompOp(x, Neq, y) } 
   | x = expr; GREATER; y = expr            { Ast.CompOp(x, Gt, y) } 
   | x = expr; LESS; y = expr               { Ast.CompOp(x, Lt, y) } 
   | x = expr; GREATEREQ; y = expr          { Ast.CompOp(x, Geq, y) } 
   | x = expr; LESSEQ; y = expr             { Ast.CompOp(x, Leq, y) } 
   ;


relOp :
   | x = expr; ANDALSO; y = expr    { Ast.RelOp(x, Ast.And, y) } 
   | x = expr; ORELSE; y = expr     { Ast.RelOp(x, Ast.Or, y) } 
   ;


matchExp :
    | MATCH; x = expr; WITH; EMPTYLIST; RIGHTARROW; y = expr; BAR; a = ID; 
      CONS; b = ID; RIGHTARROW; c = expr   { Ast.Match(x, y, a, b, c)  } %prec statement
    ;  


arg :
    | LPAREN e = expr RPAREN      { e }    
    | x = ID                      { {func_structure = Var(x); func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} } 
    | TRUE                        { {func_structure = Bool(true); func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} } 
    | FALSE                       { {func_structure = Bool(false); func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} } 
    | i = INT                     { {Ast.func_structure = Int(i); func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)} } 
    ;

app :
    | x = ID; l = nonempty_list(arg)   { Ast.App({func_structure = Ast.Var(x); func_data = Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)}::l) }
    | LPAREN; e = expr; RPAREN; l = nonempty_list(arg) { Ast.App(e::l) }
    ;

id_list:
    | x = ID;                   { Ast.Single(x, Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)) }
    | x = ID;  l = id_list      { Ast.Curry((x, Some(($startpos.Lexing.pos_lnum, $startpos.Lexing.pos_cnum - $startpos.Lexing.pos_bol + 1),
                                             ($endpos.Lexing.pos_lnum, $endpos.Lexing.pos_cnum - $endpos.Lexing.pos_bol + 1),
                                             $startpos.Lexing.pos_fname)), l) } 
    ;

lambdaExp :
    | FUN;  args = id_list; RIGHTARROW; body = expr 
                                        { Ast.Lambda(args, body)  } %prec statement
    ;

m:
    | DOLLAR { Ast.Dollar }
    | HASH   { Ast.Hash   }
    ;


linid:
    | x = ID  { x }
    ;


sharedid:
    | HASH; x = ID  { x }
    ;

branches :
    | k = ID; RRARROW; p = st; b = branches2 { (k, p)::b }    

branches2 :
    | BAR; b = branches { b }
    | RPAREN { [] }
    ;

potential :
    | LBRACE; i = INT; RBRACE { Ast.Arith(Arith.Int(i)) }
    | LBRACE; TIMES; RBRACE   { Ast.Star }
    ;

app_arg :
    | x = ID           { x }
    ;

app_arg_shared :
    | x = ID       { x }
    ;
(*
print_id:
    | x = ID                    { Ast.Word(x) }
    | PINT                      { Ast.PInt }
    | PBOOL                     { Ast.PBool }
    | PSTR                      { Ast.PStr }
    | PADDR                     { Ast.PAddr }
    | PCHAN                     { Ast.PChan }
    | NEWLINE                   { Ast.PNewline }
    ;
*)

st:
    |  x = ID; LARROW; f = ID; xs = list(ID); SEMI; p = st { {st_structure = Ast.Spawn(x, f, xs, p); st_data = Ast.make_ext $startpos $endpos(xs) } }
    |  x = ID; LARROW; f = ID; xs = list(ID)               { {st_structure = Ast.ExpName(x, f, xs); st_data = Ast.make_ext $startpos $endpos } }
    |  x = ID; FORWARD; y = ID                                          { {st_structure = Ast.Fwd(x,y); st_data = Ast.make_ext $startpos $endpos } }
    |  SEND; x = linid; w = ID; SEMI; p = st                            { {st_structure = Ast.Send(x,w,p); st_data = Ast.make_ext $startpos $endpos(w) } }
    |  y = ID; LARROW; RECV; x = linid; SEMI; p = st                    { {st_structure = Ast.Recv(x,y,p); st_data = Ast.make_ext $startpos $endpos(x) } }
    |  x = ID; DOT; k = ID; SEMI; p = st                                { {st_structure = Ast.Lab(x,k,p); st_data = Ast.make_ext $startpos $endpos(k) } }
    |  CASE; x = linid; LPAREN; b = branches                             { {st_structure = Ast.Case(x,b); st_data = Ast.make_ext $startpos $endpos } }
    |  CLOSE; x = linid                                                  { {st_structure = Ast.Close(x); st_data = Ast.make_ext $startpos $endpos } }
    |  ABORT                                                             { {st_structure = Ast.Abort; st_data = Ast.make_ext $startpos $endpos } }
    |  WAIT; x = linid; SEMI; p = st                                     { {st_structure = Ast.Wait(x,p); st_data = Ast.make_ext $startpos $endpos(x)} }
    |  IMMUT; LBRACE; p = st; RBRACE                                     { {st_structure = Ast.Immut(p); st_data = Ast.make_ext $startpos $endpos } }
    |  CONTINUE; xs = list(linid)                                        { {st_structure = Ast.Continue(xs); st_data = Ast.make_ext $startpos $endpos } }
    |  MUT; LBRACE; p = st; RBRACE                                       { {st_structure = Ast.Mut(p); st_data = Ast.make_ext $startpos $endpos } }
    |  START; x = linid; SEMI; p = st                                    { {st_structure = Ast.Start(x,p); st_data = Ast.make_ext $startpos $endpos(x) } }
    |  FINISH; x = linid; SEMI; p = st                                   { {st_structure = Ast.Finish(x,p); st_data = Ast.make_ext $startpos $endpos(x) } }
    |  MUTATE; x = linid; SEMI; p = st                                   { {st_structure = Ast.Mutate(x,p); st_data = Ast.make_ext $startpos $endpos(x) } }
    |  x1 = ID; COMMA; x2 = linid; LARROW; SPLIT; x = linid; SEMI; p = st { {st_structure = Ast.Split(x1,x2,x,p); st_data = Ast.make_ext $startpos $endpos(x) } }
    |  x = ID; LARROW; MERGE; x1 = linid; COMMA; x2 = linid; SEMI; p = st { {st_structure = Ast.Merge(x,x1,x2,p); st_data = Ast.make_ext $startpos $endpos(x) } }
    |  SHARE; x = linid; SEMI; p = st                                    { {st_structure = Ast.Share(x,p); st_data = Ast.make_ext $startpos $endpos(x) } }
    |  OWN; x = linid; SEMI; p = st                                      { {st_structure = Ast.Own(x,p); st_data = Ast.make_ext $startpos $endpos(x) } }
    |  SEND; x = linid; LBRACE; w = ID; RBRACE; SEMI; p = st             { {st_structure = Ast.SendId(x,w,p); st_data = Ast.make_ext $startpos $endpos(w) } }
    |  LBRACE; y = ID; RBRACE; LARROW; RECV; x = linid; SEMI; p = st     { {st_structure = Ast.RecvId(x,y,p); st_data = Ast.make_ext $startpos $endpos(x) } }
    |  SEND; x = linid; LBRACE; LBRACE; w = perm; RBRACE; RBRACE; SEMI; p = st  { {st_structure = Ast.SendPerm(x,w,p); st_data = Ast.make_ext $startpos $endpos(w) } }
    |  LBRACE; LBRACE; y = ID; RBRACE; RBRACE; LARROW; RECV; x = linid; SEMI; p = st     { {st_structure = Ast.RecvPerm(x,y,p); st_data = Ast.make_ext $startpos $endpos(x) } }
    |  WORK; pot = potential; SEMI; p = st                               { {st_structure = Ast.Work(pot, p); st_data = Ast.make_ext $startpos $endpos(pot)} }
    |  DEPOSIT; pot = potential; SEMI; p = st                            { {st_structure = Ast.Deposit(pot, p); st_data = Ast.make_ext $startpos $endpos(pot)} }
    |  PAY; x = linid; pot = potential; SEMI; p = st                     { {st_structure = Ast.Pay(x, pot, p); st_data = Ast.make_ext $startpos $endpos(pot)} }
    |  GET; x = linid; pot = potential; SEMI; p = st                     { {st_structure = Ast.Get(x, pot, p); st_data = Ast.make_ext $startpos $endpos(pot)} }
    |  y = ID; LARROW; ACQUIRE; x = sharedid; SEMI; p = st              { {st_structure = Ast.Acquire(x,y,p); st_data = Ast.make_ext $startpos $endpos(x)} }
    |  y = ID; LARROW; ACCEPT; x = sharedid; SEMI; p = st               { {st_structure = Ast.Accept(x,y,p); st_data = Ast.make_ext $startpos $endpos(x)} }
    |  y = ID; LARROW; RELEASE; x = linid; SEMI; p = st                 { {st_structure = Ast.Release(x,y,p); st_data = Ast.make_ext $startpos $endpos(x)} }
    |  y = ID; LARROW; DETACH; x = linid; SEMI; p = st                  { {st_structure = Ast.Detach(x,y,p); st_data = Ast.make_ext $startpos $endpos(x)} }
    |  LET; x = ID; EQUALS; e = expr; SEMI; p = st                       { {st_structure = Ast.Let(x,e,p); st_data = Ast.make_ext $startpos $endpos(e)} }
    |  IF; ifE = expr; THEN; thenE = st; ELSE; elseE = st                    { {Ast.st_structure = Ast.IfS(ifE, thenE, elseE); st_data = Ast.make_ext $startpos $endpos } }
    |  PRINT; LPAREN; l = QUOTED_STRING; RPAREN; SEMI; p = st    { {Ast.st_structure = Ast.Print(List.rev l, [], p); st_data = Ast.make_ext $startpos $endpos(l)} }
    |  PRINT; LPAREN; l = QUOTED_STRING; COMMA; args = separated_list(COMMA, app_arg); RPAREN; SEMI; p = st         { {Ast.st_structure = Ast.Print(List.rev l, args, p); st_data = Ast.make_ext $startpos $endpos(args)} }
    ;
