(* import *)
%token <string> IMPORT
(* functional layer *)
/* %token <int> INT */
%token ONE
%token <float> FLOAT
%token <string> ID
%token <Ast.printable list> QUOTED_STRING
%token LPAREN RPAREN
%token EMPTYLIST LSQUARE RSQUARE COMMA
%token EQUALS
%token BAR
%token PLUS TIMES
%token EOF
%token TYPE PROC TURNSTILE EXEC COLON
(* printing *)
%token PRINT
(* session type layer *)
%token LOLLI AMPERSAND UP DOWN DOUBLEDOWN QUESTION BANG LANGLE RANGLE
%token LBRACE RBRACE
%token FORWARD LARROW SEMI RRARROW
%token RECV SEND CASE DOT CLOSE WAIT ABORT
%token IMMUT CONTINUE MUT START FINISH MUTATE SPLIT MERGE SHARE OWN
%start <Ast.file> file
%%


file:
  | imports = list(import); vl = list(decl) EOF { (imports, vl) }
  ;

import:
  | p = IMPORT { p }
  ;

label_proto:
    | l = ID; COLON; t = proto         { (l,t) }
    ;

argument:
    | LPAREN; l = ID; COLON; t = stype; RPAREN     { (l,t) }
    ;

args_opt:
    | DOT                                   { [] }
    | l = separated_list(COMMA, argument)   { l }
    ;

perm_term:
    | coef = FLOAT; TIMES; var = ID; { (var, Q.of_float coef) }
    | var = ID; TIMES; coef = FLOAT; { (var, Q.of_float coef) }
    | var = ID;                      { (var, Q.one) }
    | const = FLOAT;                 { ("", Q.of_float const) }
    | ONE;                           { ("", Q.one) }
    | ONE; TIMES; var = ID;          { (var, Q.one) }
    | var = ID; TIMES; ONE;          { (var, Q.one) }

perm:
    | TIMES;                                         { Ast.Owned }
    | ps = separated_nonempty_list(PLUS, perm_term); { Ast.Fractional (Ast.StringMap.of_seq (List.to_seq ps)) }

stype:
    | LANGLE; t = proto; COMMA; p = perm; COMMA; a = ID; RANGLE { (t,p,a) }
    ;

proto:
    | PLUS; LBRACE; choices = separated_list(COMMA, label_proto); RBRACE        { Ast.Plus(choices) }
    | AMPERSAND; LBRACE; choices = separated_list(COMMA, label_proto); RBRACE   { Ast.With(choices) }
    | s = stype; TIMES; t = proto                                               { Ast.Tensor(s,t) }
    | s = stype; LOLLI; t = proto                                               { Ast.Lolli(s,t) }
    | ONE                                                                       { Ast.One }
    | UP; k = ID; DOT; t = proto                                                { Ast.Up(k,t) }
    | DOWN; t = proto                                                           { Ast.Down(t) }
    | DOUBLEDOWN; t = proto                                                     { Ast.DoubleDown(t) }
    | QUESTION; a = ID; DOT; t = proto                                          { Ast.ExistsId(a,t) }
    | BANG; a = ID; DOT; t = proto                                              { Ast.ForallId(a,t) }
    | QUESTION; QUESTION; a = ID; DOT; t = proto                                { Ast.ExistsPerm(a,t) }
    | BANG; BANG; a = ID; DOT; t = proto                                        { Ast.ForallPerm(a,t) }
    | x = ID                                                                    { Ast.TpName(x) }
    | LPAREN; s = proto; RPAREN                                                 { s }
    ;

decl:
    | TYPE; x = ID; EQUALS; t = proto                                                                                                           { (Ast.TpDef (x,t), Ast.make_ext $startpos $endpos) }
    | PROC; f = ID; ids = id_list; ps = permname_list; COLON; args = args_opt; TURNSTILE; LPAREN; c = ID; COLON; t = proto; RPAREN; EQUALS; e = st  { (Ast.ExpDecDef(f, (ids, ps, args, (c,t)), e), Ast.make_ext $startpos $endpos) }
    | EXEC; f = ID; l = list(ID)                                                                                                                { (Ast.Exec(f,l), Ast.make_ext $startpos $endpos) }
    ;

branches:
    | k = ID; RRARROW; p = st; b = branches2 { (k, p)::b }    

branches2:
    | BAR; b = branches { b }
    | RPAREN { [] }
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

id_list:
    | { [] }
    | EMPTYLIST { [] }
    | LSQUARE; ids = separated_list(COMMA, ID); RSQUARE { ids }
    ;

permname_list:
    | { [] }
    | LBRACE; ids = separated_list(COMMA, ID); RBRACE { ids }

perm_list:
    | { [] }
    | LBRACE; ids = separated_list(COMMA, perm); RBRACE { ids }

st:
    |  LBRACE; a = ID; RBRACE; COMMA; x = ID; LARROW; f = ID; ids = id_list; ps = perm_list xs = list(ID); SEMI; p = st  { {st_structure = Ast.Spawn(a, x, f, ids, ps, xs, p); st_data = Ast.make_ext $startpos $endpos(xs) } }
    |  x = ID; LARROW; f = ID; ids = id_list; ps = perm_list; xs = list(ID)                                              { {st_structure = Ast.ExpName(x, f, ids, ps, xs); st_data = Ast.make_ext $startpos $endpos } }
    |  x = ID; FORWARD; y = ID                                                                                           { {st_structure = Ast.Fwd(x,y); st_data = Ast.make_ext $startpos $endpos } }
    |  SEND; x = ID; w = ID; SEMI; p = st                                                                                { {st_structure = Ast.Send(x,w,p); st_data = Ast.make_ext $startpos $endpos(w) } }
    |  y = ID; LARROW; RECV; x = ID; SEMI; p = st                                                                        { {st_structure = Ast.Recv(x,y,p); st_data = Ast.make_ext $startpos $endpos(x) } }
    |  x = ID; DOT; k = ID; SEMI; p = st                                                                                 { {st_structure = Ast.Lab(x,k,p); st_data = Ast.make_ext $startpos $endpos(k) } }
    |  CASE; x = ID; LPAREN; b = branches                                                                                { {st_structure = Ast.Case(x,b); st_data = Ast.make_ext $startpos $endpos } }
    |  CLOSE; x = ID                                                                                                     { {st_structure = Ast.Close(x); st_data = Ast.make_ext $startpos $endpos } }
    |  ABORT                                                                                                             { {st_structure = Ast.Abort; st_data = Ast.make_ext $startpos $endpos } }
    |  WAIT; x = ID; SEMI; p = st                                                                                        { {st_structure = Ast.Wait(x,p); st_data = Ast.make_ext $startpos $endpos(x)} }
    |  IMMUT; xs = list(ID); LBRACE; per = ID; RRARROW; p = st; RBRACE                                                   { {st_structure = Ast.Immut(xs,per,p); st_data = Ast.make_ext $startpos $endpos } }
    |  CONTINUE; xs = list(ID)                                                                                           { {st_structure = Ast.Continue(xs); st_data = Ast.make_ext $startpos $endpos } }
    |  MUT; LBRACE; p = st; RBRACE                                                                                       { {st_structure = Ast.Mut(p); st_data = Ast.make_ext $startpos $endpos } }
    |  START; x = ID; LBRACE; per = perm; RBRACE; SEMI; p = st                                                           { {st_structure = Ast.Start(x,per,p); st_data = Ast.make_ext $startpos $endpos(x) } }
    |  FINISH; x = ID; SEMI; p = st                                                                                      { {st_structure = Ast.Finish(x,p); st_data = Ast.make_ext $startpos $endpos(x) } }
    |  MUTATE; x = ID; SEMI; p = st                                                                                      { {st_structure = Ast.Mutate(x,p); st_data = Ast.make_ext $startpos $endpos(x) } }
    |  x1 = ID; COMMA; x2 = ID; LARROW; SPLIT; x = ID; SEMI; p = st                                                      { {st_structure = Ast.Split(x1,x2,x,p); st_data = Ast.make_ext $startpos $endpos(x) } }
    |  x = ID; LARROW; MERGE; x1 = ID; COMMA; x2 = ID; SEMI; p = st                                                      { {st_structure = Ast.Merge(x,x1,x2,p); st_data = Ast.make_ext $startpos $endpos(x) } }
    |  SHARE; x = ID; SEMI; p = st                                                                                       { {st_structure = Ast.Share(x,p); st_data = Ast.make_ext $startpos $endpos(x) } }
    |  OWN; x = ID; SEMI; p = st                                                                                         { {st_structure = Ast.Own(x,p); st_data = Ast.make_ext $startpos $endpos(x) } }
    |  SEND; x = ID; LBRACE; w = ID; RBRACE; SEMI; p = st                                                                { {st_structure = Ast.SendId(x,w,p); st_data = Ast.make_ext $startpos $endpos(w) } }
    |  LBRACE; y = ID; RBRACE; LARROW; RECV; x = ID; SEMI; p = st                                                        { {st_structure = Ast.RecvId(x,y,p); st_data = Ast.make_ext $startpos $endpos(x) } }
    |  SEND; x = ID; LBRACE; LBRACE; w = perm; RBRACE; RBRACE; SEMI; p = st                                              { {st_structure = Ast.SendPerm(x,w,p); st_data = Ast.make_ext $startpos $endpos(w) } }
    |  LBRACE; LBRACE; y = ID; RBRACE; RBRACE; LARROW; RECV; x = ID; SEMI; p = st                                        { {st_structure = Ast.RecvPerm(x,y,p); st_data = Ast.make_ext $startpos $endpos(x) } }
    |  PRINT; LPAREN; l = QUOTED_STRING; RPAREN; SEMI; p = st                                                            { {Ast.st_structure = Ast.Print(List.rev l, [], p); st_data = Ast.make_ext $startpos $endpos(l)} }
    |  PRINT; LPAREN; l = QUOTED_STRING; COMMA; args = separated_list(COMMA, ID); RPAREN; SEMI; p = st                   { {Ast.st_structure = Ast.Print(List.rev l, args, p); st_data = Ast.make_ext $startpos $endpos(args)} }
    ;
