(* Type Checking *)
(* Use the syntax-directed rules to check the types and
* raises ErrorMsg.Error if an error is discovered
*)

module R = Arith
module A = Ast
module PP = Pprint
module E = TpError
(* module I = Infer *)
module F = FracFlags
module M = Core.Map

let error = ErrorMsg.error ErrorMsg.Type
(* let linkerror = ErrorMsg.error ErrorMsg.Link;; *)

(*********************)
(* Validity of types *)
(*********************)


(*
  Equi-Synchronizing Session Types
  Purely linear types are always equi-synchronizing
*)

(* let rec esync env seen tp c ext is_shared =
     if !F.verbosity >= 3
     then print_string ("checking esync: \n" ^ PP.pp_tp env tp ^ "\n" ^ PP.pp_tp env c ^ "\n") ;
     match tp with
         A.Plus(choice) -> esync_choices env seen choice c ext is_shared
       | A.With(choice) -> esync_choices env seen choice c ext is_shared
       | A.Tensor(_a,b,_m) -> esync env seen b c ext is_shared
       | A.Lolli(_a,b,_m) -> esync env seen b c ext is_shared
       | A.One -> if is_shared then error ext ("type not equi-synchronizing") else ()
       | A.PayPot(_pot,a) -> esync env seen a c ext is_shared
       | A.GetPot(_pot,a) -> esync env seen a c ext is_shared
       | A.TpName(v) ->
           begin
             try
               if List.exists (fun x -> x = v) seen
               then ()
               else esync env (v::seen) (A.expd_tp env v) c ext is_shared
             with
               A.UndeclaredTp -> error ext ("type " ^ v ^ " undeclared")
           end
       | A.Up(a) -> esync env seen a c ext true
       | A.Down(a) -> esync env seen a c ext true
       | A.FArrow(_t,a) -> esync env seen a c ext is_shared
       | A.FProduct(_t,a) -> esync env seen a c ext is_shared
       | A.FMap _ -> if is_shared then error ext ("type not equi-synchronizing") else ()
       | A.STMap _ -> if is_shared then error ext ("type not equi-synchronizing") else ()
       | A.Coin -> if is_shared then error ext ("type not equi-synchronizing") else ()

   and esync_choices env seen cs c ext is_shared = match cs with
       (_l,a)::as' -> esync env seen a c ext is_shared ; esync_choices env seen as' c ext is_shared
     | [] -> ();;

   let esync_tp env tp ext = esync env [] tp tp ext false;; *)

(***********************)
(* Properties of types *)
(***********************)

let contractive tp = match tp with
    A.TpName(_a) -> false
  | A.Plus _ | A.With _
  | A.Tensor _ | A.Lolli _
  | A.One
  | A.Up _ | A.Down _ | A.DoubleDown _
  | A.ExistsId _ | A.ForallId _
  | A.ExistsPerm _ | A.ForallPerm _ -> true

(*****************)
(* Type equality *)
(*****************)


(* Type equality, equirecursively defined *)

(* Structural equality *)


let rec mem_seen env seen a a' = match seen with
    (b,b')::seen' ->
      if b = a && b' = a' then true
      else if b = a' && b' = a
      then true
      else mem_seen env seen' a a'
  | [] -> false


(* eq_tp env con seen A A' = true if (A = A'), defined coinductively *)
let rec eq_tp' env seen a a' =
  if !F.verbosity >= 3
  then print_string ("comparing " ^ PP.pp_tp env a ^ " and " ^ PP.pp_tp env a' ^ "\n")
  else ()
  ; eq_tp env seen a a'

and eq_tp env seen tp tp' = match tp, tp' with
    A.Plus(choice), A.Plus(choice') ->
      eq_choice env seen choice choice'
  | A.With(choice), A.With(choice') ->
      eq_choice env seen choice choice'
  | A.Tensor((s,p,a),t), A.Tensor((s',p',a'),t') ->
    (* TODO: better permission equality *)
      a = a' && p = p' && eq_tp' env seen s s' && eq_tp' env seen t t'
  | A.Lolli((s,p,a),t), A.Lolli((s',p',a'),t') ->
      a = a' && p = p' && eq_tp' env seen s s' && eq_tp' env seen t t'
  | A.One, A.One -> true

  | A.Up(a), A.Up(a') ->
      eq_tp' env seen a a'
  | A.Down(a), A.Down(a') ->
      eq_tp' env seen a a'
  | A.DoubleDown(a), A.DoubleDown(a') ->
      eq_tp' env seen a a'

  | A.ExistsId(x,a), A.ExistsId(x',a') ->
    x = x' && eq_tp' env seen a a'
  | A.ForallId(x,a), A.ForallId(x',a') ->
    x = x' && eq_tp' env seen a a'
  | A.ExistsPerm(x,a), A.ExistsId(x',a') ->
    x = x' && eq_tp' env seen a a'
  | A.ForallPerm(x,a), A.ForallPerm(x',a') ->
    x = x' && eq_tp' env seen a a'

  | A.TpName(a), A.TpName(a') ->
      eq_name_name env seen a a' (* coinductive type equality *)
  | A.TpName(a), a' ->
      eq_tp' env seen (A.expd_tp env a) a'
  | a, A.TpName(a') ->
      eq_tp' env seen a (A.expd_tp env a')

  | _a, _a' -> false

and eq_choice env seen cs cs' = match cs, cs' with
    [], [] -> true
  | (l,a)::choice, (l',a')::choice' -> (* order must be equal *)
      l = l' && eq_tp' env seen a a'
      && eq_choice env seen choice choice'
  | _cs, [] -> false
  | [], _cs' -> false

and eq_name_name env seen a a' =
  if mem_seen env seen a a' then true
  else eq_tp' env ((a,a')::seen) (A.expd_tp env a) (A.expd_tp env a')

let eqtp env tp tp' = eq_tp' env [] tp tp'

(* ******************* *)
(* Subtyping Algorithm *)
(* ******************* *)

(* let rec sub_tp' env seen a a' =
     if !F.verbosity >= 3
     then print_string ("comparing " ^ PP.pp_tp env a ^ " and " ^ PP.pp_tp env a' ^ "\n")
     else ()
     ; sub_tp env seen a a'

   and sub_tp env seen tp tp' = match tp, tp' with
       A.Plus(choice), A.Plus(choice') ->
         sub_ichoice env seen choice choice'
     | A.With(choice), A.With(choice') ->
         sub_echoice env seen choice choice'
     | A.Tensor(s,t,m), A.Tensor(s',t',m') ->
         eqmode m m' && sub_tp' env seen s s' && sub_tp' env seen t t'
     | A.Lolli(s,t,m), A.Lolli(s',t',m') ->
         eqmode m m' && sub_tp' env seen s' s && sub_tp' env seen t t'
     | A.One, A.One -> true

     | A.PayPot(pot,a), A.PayPot(pot',a') ->
         eq pot pot' && sub_tp' env seen a a'
     | A.GetPot(pot,a), A.GetPot(pot',a') ->
         eq pot pot' && sub_tp' env seen a a'

     | A.Up(a), A.Up(a') ->
         sub_tp' env seen a a'
     | A.Down(a), A.Down(a') ->
         sub_tp' env seen a a'

     | A.FArrow(t,a), A.FArrow(t',a') ->
         eq_ftp t t' && sub_tp' env seen a a'
     | A.FProduct(t,a), A.FProduct(t',a') ->
         eq_ftp t t' && sub_tp' env seen a a'

     | A.FMap(kt,vt), A.FMap(kt',vt') ->
         eq_ftp kt kt' && eq_ftp vt vt'
     | A.STMap(kt,a), A.STMap(kt',a') ->
         eq_ftp kt kt' && sub_tp' env seen a a'

     | A.Coin, A.Coin -> true

     | A.TpName(a), A.TpName(a') ->
         sub_name_name env seen a a' (\* coinductive subtyping *\)
     | A.TpName(a), a' ->
         sub_tp' env seen (A.expd_tp env a) a'
     | a, A.TpName(a') ->
         sub_tp' env seen a (A.expd_tp env a')

     | _a, _a' -> false

   and sub_ichoice env seen cs cs' = match cs with
       [] -> true
     | (l,a)::choice ->
         let lab_match = List.find_all (fun (l', _) -> l = l') cs' in
         if (List.length lab_match != 1)
         then false
         else let (_, a') = List.nth lab_match 0 in
         sub_tp' env seen a a' && sub_ichoice env seen choice cs'

   and sub_echoice env seen cs cs' = match cs' with
       [] -> true
     | (l',a')::choice ->
         let lab_match = List.find_all (fun (l, _) -> l = l') cs in
         if (List.length lab_match != 1)
         then false
         else let (_, a) = List.nth lab_match 0 in
         sub_tp' env seen a a' && sub_echoice env seen cs choice

   and sub_name_name env seen a a' =
     if mem_seen env seen a a' then true
     else sub_tp' env ((a,a')::seen) (A.expd_tp env a) (A.expd_tp env a');;

   let subtp env tp tp' = sub_tp' env [] tp tp';; *)

(*************************************)
(* Type checking process expressions *)
(*************************************)

(* exception UnknownTypeError;; *)

let chan_of (c, _tp) = c
let tp_of (_c, tp) = tp
(* let name_of (_s,c,_m) = c;; *)

(*
let eq_str (s1,_c1,_m1) (s2,_c2,_m2) = s1 = s2;;
*)

(* let eq_name (_s1,c1,_m1) (_s2,c2,_m2) = c1 = c2;;

   let eq_mode (_s1,_c1,m1) (_s2,_c2,m2) = eqmode m1 m2;;

   let eq_chan c1 c2 =
     eq_name c1 c2 && eq_mode c1 c2;;

   let rec checktp c delta = match delta with
       [] -> false
     | (x,_t)::delta' ->
         if eq_name x c then true
         else checktp c delta';;

   let rec checkftp v odelta = match odelta with
       [] -> false
     | (A.STyped _)::odelta' -> checkftp v odelta'
     | (A.Functional (w,_t))::odelta' ->
         if w = v then true
         else checkftp v odelta';;

   let check_ftp v delta =
     let {A.shared = _sdelta ; A.linear = _ldelta ; A.ordered = odelta} = delta in
     checkftp v odelta;;

   let check_tp c delta =
     let {A.shared = sdelta ; A.linear = ldelta ; A.ordered = _odelta} = delta in
     checktp c sdelta || checktp c ldelta;;

   let check_stp c delta =
     let {A.shared = sdelta ; A.linear = _ldelta ; A.ordered = _odelta} = delta in
       checktp c sdelta;;

   let check_ltp c delta =
     let {A.shared = _sdelta ; A.linear = ldelta ; A.ordered = _odelta} = delta in
       checktp c ldelta;;

   let rec pure delta = match delta with
       [] -> true
     | (c,_t)::delta' ->
         if not (mode_P c)
         then false
         else pure delta';;

   let purelin delta =
     let {A.shared = _sdelta ; A.linear = ldelta ; A.ordered = _odelta} = delta in
     pure ldelta;;

   (\* must check for existence first *\)
   let rec findtp c delta ext = match delta with
       [] -> raise UnknownTypeError
     | (x,t)::delta' ->
         if eq_chan x c then t
         else findtp c delta' ext;;

   let rec findftp v delta = match delta with
       [] -> raise UnknownTypeError
     | (A.Functional (w,t))::delta' ->
         if v = w then t
         else findftp v delta'
     | (A.STyped _)::delta' ->
         findftp v delta';;

   let find_ftp v delta =
     let {A.shared = _sdelta ; A.linear = _ldelta ; A.ordered = odelta} = delta in
     findftp v odelta;;

   let find_stp c delta ext =
     let {A.shared = sdelta ; A.linear = _ldelta ; A.ordered = _odelta} = delta in
     if not (mode_S c)
     then error ext ("mode of channel " ^ PP.pp_chan c ^ " not S")
     else findtp c sdelta ext;;

   let find_ltp c delta ext =
     let {A.shared = _sdelta ; A.linear = ldelta ; A.ordered = _odelta} = delta in
     if not (mode_lin c)
     then E.error_mode_shared_comm c ext
     else findtp c ldelta ext;;

   let rec find_sltp x sdelta ldelta = match sdelta, ldelta with
       [], [] -> raise UnknownTypeError
     | (y,t1)::sdelta', (z,t2)::ldelta' ->
         if eq_name x y
         then (y,t1)
         else if eq_name x z
         then (z,t2)
         else find_sltp x sdelta' ldelta'
     | (y,t)::sdelta', [] ->
         if eq_name x y
         then (y,t)
         else find_sltp x sdelta' []
     | [], (z,t)::ldelta' ->
         if eq_name x z
         then (z,t)
         else find_sltp x [] ldelta';;

   let find_tp x delta =
     let {A.shared = sdelta ; A.linear = ldelta ; A.ordered = _odelta} = delta in
     find_sltp x sdelta ldelta;;

   let rec removetp x delta = match delta with
       [] -> []
     | (y,t)::delta' ->
         if eq_name x y
         then delta'
         else (y,t)::(removetp x delta');;

   let rec removeotp x odelta = match odelta with
       [] -> []
     | a::odelta' ->
         match a with
             A.Functional(v,t) -> (A.Functional(v,t))::(removeotp x odelta')
           | A.STyped (y,t) ->
               if eq_name x y
               then odelta'
               else (A.STyped(y,t))::(removeotp x odelta');;

   let remove_tp x delta =
     let {A.shared = sdelta ; A.linear = ldelta ; A.ordered = odelta} = delta in
     {A.shared = removetp x sdelta ; A.linear = removetp x ldelta ; A.ordered = removeotp x odelta};;

   let add_chan env (x,a) delta =
     let {A.shared = sdelta ; A.linear = ldelta ; A.ordered = odelta} = delta in
     if A.is_shared env a
     then {A.shared = (x,a)::sdelta ; A.linear = ldelta ; A.ordered = (A.STyped (x,a))::odelta}
     else {A.shared = sdelta ; A.linear = (x,a)::ldelta ; A.ordered = (A.STyped (x,a))::odelta};;

   let add_var (v,t) delta =
     let {A.shared = sdelta ; A.linear = ldelta ; A.ordered = odelta} = delta in
     let odelta' = (A.Functional(v,t))::odelta in
     {A.shared = sdelta ; A.linear = ldelta ; A.ordered = odelta'};;

   let update_tp env x t delta =
     let delta = remove_tp x delta in
     add_chan env (x,t) delta;;

   let rec match_ctx env sig_ctx ctx delta sig_len len ext = match sig_ctx, ctx with
       (A.STyped (sc,st))::sig_ctx', (A.STArg c)::ctx' ->
         begin
           if not (check_tp c delta)
           then error ext ("unknown or duplicate variable: " ^ PP.pp_chan c)
           else if not (eq_mode sc c)
           then E.error_mode_mismatch (sc, c) ext
           else
             let {A.shared = sdelta ; A.linear = _ldelta ; A.ordered = _odelta} = delta in
             if checktp c sdelta
             then
               begin
                 let t = find_stp c delta ext in
                 (\* "subtype is sufficient with subsync types" *\)
                 if subtp env t st
                 then match_ctx env sig_ctx' ctx' delta sig_len len ext
                 else error ext ("shared type mismatch: type of " ^ PP.pp_chan c ^ " : " ^ PP.pp_tp_compact env t ^
                             " does not match type in declaration: " ^ PP.pp_tp_compact env st)
               end
             else
               begin
                 let t = find_ltp c delta ext in
                 (\* "subtype is sufficient with subsync types" *\)
                 if subtp env t st
                 then match_ctx env sig_ctx' ctx' (remove_tp c delta) sig_len len ext
                 else error ext ("linear type mismatch: type of " ^ PP.pp_chan c ^ " : " ^ PP.pp_tp_compact env t ^
                             " does not match type in declaration: " ^ PP.pp_tp_compact env st)
               end
         end
     | (A.Functional (_sv,st))::sig_ctx', (A.FArg (A.Var v))::ctx' ->
         begin
           if not (check_ftp v delta)
           then error ext ("unknown or duplicate variable: " ^ v)
           else
             let t = find_ftp v delta in
             if eq_ftp st t
             then match_ctx env sig_ctx' ctx' delta sig_len len ext
             else error ext ("functional type mismatch: type of " ^ v ^ " : " ^ PP.pp_ftp_simple t ^
                         " does not match type in declaration: " ^ PP.pp_ftp_simple st)
         end
     | [], [] -> delta
     | _, _ -> error ext ("process defined with " ^ string_of_int sig_len ^
               " arguments but called with " ^ string_of_int len ^ " arguments");;

   let join delta =
     let {A.shared = _sdelta ; A.linear = _ldelta ; A.ordered = odelta} = delta in
     odelta;;

   let rec lookup_var x odelta = match odelta with
       A.Functional(y,t)::odelta' -> if x = y then Some t else lookup_var x odelta'
     | A.STyped _::odelta' -> lookup_var x odelta'
     | [] -> None;;

   let lookup_ftp x delta ext =
     let {A.shared = _sdelta; A.linear = _ldelta; A.ordered = odelta} = delta in
     match lookup_var x odelta with
         None -> error ext ("unknown variable " ^ x)
       | Some t -> t;;

   let min_potential pot pot' =
     if not (eq pot pot')
     then raise UnknownTypeError
     else pot;;

   let rec min_tp t t' = match t, t' with
       A.Integer, A.Integer -> A.Integer
     | A.Boolean, A.Boolean -> A.Boolean
     | A.Arrow(t1,t2), A.Arrow(t1',t2') -> A.Arrow(min_tp t1 t1', min_tp t2 t2')
     | A.ListTP(t1,pot), A.ListTP(t1',pot') -> A.ListTP(min_tp t1 t1', min_potential pot pot')
     | _t, _t' -> raise UnknownTypeError;;

   let rec min_delta odelta1 odelta2 = match odelta1 with
       A.STyped(x,a)::odelta1' -> A.STyped(x,a)::(min_delta odelta1' odelta2)
     | A.Functional(v,t1)::odelta1' ->
         begin
           match lookup_var v odelta2 with
               None -> min_delta odelta1' odelta2
             | Some t2 -> A.Functional(v, min_tp t1 t2)::(min_delta odelta1' odelta2)
         end
     | [] -> [];;

   let min_pot (delta1, pot1) (delta2, pot2) =
     let {A.shared = sdelta1 ; A.linear = ldelta1 ; A.ordered = odelta1} = delta1 in
     let {A.shared = _sdelta2 ; A.linear = _ldelta2 ; A.ordered = odelta2} = delta2 in
     ({A.shared = sdelta1; A.linear = ldelta1; A.ordered = min_delta odelta1 odelta2}, min_potential pot1 pot2);;

   let rec removevar x odelta = match odelta with
       [] -> []
     | A.Functional (y,t)::odelta' -> if x = y then odelta' else (A.Functional (y,t))::(removevar x odelta')
     | A.STyped(c,a)::odelta' -> (A.STyped (c,a))::(removevar x odelta');;

   let remove_var x delta =
     {A.shared = delta.A.shared; A.linear = delta.A.linear; A.ordered = removevar x delta.A.ordered};;

   let rec consume_pot tp = match tp with
       A.Integer | A.Boolean | A.String | A.Address | A.VarT _ -> tp
     | A.ListTP(t,_pot) -> A.ListTP(consume_pot t, A.Arith (R.Int(0)))
     | A.Arrow(t1,t2) -> A.Arrow(consume_pot t1, consume_pot t2);;

   let rec consumevar x odelta = match odelta with
       [] -> []
     | A.STyped(c,a)::odelta' -> (A.STyped(c,a))::(consumevar x odelta')
     | A.Functional(y,t)::odelta' ->
         if x = y
         then (A.Functional(y,consume_pot t))::odelta'
         else (A.Functional(y,t))::odelta';;

   let consume x delta =
     {A.shared = delta.A.shared; A.linear = delta.A.linear; A.ordered = consumevar x delta.A.ordered};;

   let rec consify l = match l with
       [] -> A.ListE([])
     | e::es ->
         let d = e.A.func_data in
         A.Cons(e, {A.func_data = d; A.func_structure = consify es});;

   let tc_printable_arg arg t_exp_opt delta ext =
     match arg with
         A.FArg (A.Var v) ->
           begin
             if not (check_ftp v delta)
             then error ext ("unknown or duplicate variable: " ^ v)
             else
             let t = find_ftp v delta in
             match t_exp_opt with
                 None -> error ext ("invalid type of " ^ v ^ ", expected: channel, found: " ^ PP.pp_ftp_simple t)
               | Some t_exp ->
                   if eq_ftp t_exp t
                   then ()
                   else error ext ("invalid type of " ^ v ^
                                   ", expected: " ^ PP.pp_ftp_simple t_exp ^ ", found: " ^ PP.pp_ftp_simple t)
           end
       | A.FArg _e -> raise UnknownTypeError
       | A.STArg c ->
           if not (check_tp c delta)
           then error ext ("unknown or duplicate variable: " ^ PP.pp_chan c)
           else
           match t_exp_opt with
               None -> ()
             | Some t_exp -> error ext ("invalid type of " ^ PP.pp_chan c ^ ", expected: " ^
                                        PP.pp_ftp_simple t_exp ^ ", found: channel");;

   let rec check_printable_list delta ext plist arglist plen arglen =
     match plist, arglist with
         [], [] -> ()
       | A.Word(_)::ps, _ -> check_printable_list delta ext ps arglist plen arglen
       | A.PNewline::ps, _ -> check_printable_list delta ext ps arglist plen arglen
       | A.PInt::ps, arg::args ->
           let () = tc_printable_arg arg (Some A.Integer) delta ext in
           check_printable_list delta ext ps args plen arglen
       | A.PBool::ps, arg::args ->
           let () = tc_printable_arg arg (Some A.Boolean) delta ext in
           check_printable_list delta ext ps args plen arglen
       | A.PStr::ps, arg::args ->
           let () = tc_printable_arg arg (Some A.String) delta ext in
           check_printable_list delta ext ps args plen arglen
       | A.PAddr::ps, arg::args ->
           let () = tc_printable_arg arg (Some A.Address) delta ext in
           check_printable_list delta ext ps args plen arglen
       | A.PChan::ps, arg::args ->
           let () = tc_printable_arg arg None delta ext in
           check_printable_list delta ext ps args plen arglen
       | _, _ ->
           error ext ("print string expects " ^ string_of_int plen ^
                     " arguments but called with " ^ string_of_int arglen ^ " arguments");;

   let is_argtype p = match p with
       A.Word _ | A.PNewline -> false
     | A.PInt | A.PBool | A.PStr | A.PAddr | A.PChan -> true;;

   let filter_args l = List.filter (fun p -> is_argtype p) l;; *)

let is_tpdef env a = match A.lookup_tp env a with None -> false | Some _ -> true;;
let is_expdecdef env f = match A.lookup_expdef env f with None -> false | Some _ -> true;;

let rec check_declared env ext a = match a with
    A.Plus(choices) | A.With(choices) -> check_declared_choices env ext choices
  | A.Tensor((a1,_,_),a2) | A.Lolli((a1,_,_),a2) ->
    let () = check_declared env ext a1 in
    check_declared env ext a2
  | A.One -> ()
  | A.TpName(v) ->
    if is_tpdef env v
    then ()
    else error ext ("type name " ^ v ^ " undeclared")
  | A.Up(a') | A.Down(a') | A.DoubleDown(a') | A.ExistsId(_, a')
  | A.ForallId(_, a') | A.ExistsPerm(_, a') | A.ForallPerm(_, a') -> check_declared env ext a'

and check_declared_choices env ext cs = match cs with
    [] -> ()
  | (_,a)::cs' ->
    let () = check_declared env ext a in
    check_declared_choices env ext cs';;

let rec check_declared_list env ext args = match args with
  | (_c,(a,_,_))::args' ->
    let () = check_declared env ext a in
    check_declared_list env ext args'
  | [] -> ()


let rec checkexp trace env ctx p zc ext = check_exp' trace env ctx p zc ext

and check_exp' trace env ctx p zc ext =
begin
    if trace
    then print_string (PP.pp_exp_prefix (p.A.st_structure) ^ " : "
                        ^ PP.pp_tpj_compact env ctx zc ^ "\n")
    else ()
end
; check_exp trace env ctx p zc ext


(* judgmental constructs: id, cut, spawn, call *)
and check_exp trace env ctx exp zc ext = match (exp.A.st_structure) with
    A.Fwd(x,y) ->
    begin
      let {A.idnames = idnames ; A.permnames = permnames ; A.owned = owned ; A.locked = ldelta ; A.linear = delta} = ctx in
      let () =
        if List.length owned > 0 then
          error (exp.A.st_data) ("forward with owned channels " ^ PP.pp_channames owned)
        else if List.length ldelta > 0 then
          error (exp.A.st_data) ("forward with locked channels " ^ PP.pp_chantp_list ldelta)
        else ()
      in
      let tx = chan_of zc in
      let () =
        if x <> tx then
          error (exp.A.st_data) ("forward to " ^ x ^ " instead of expected " ^ tx)
        else ()
      in
      let c = tp_of zc in
      let (ty, (a, p, id)) = List.hd delta in
      if List.length ldelta <> 1 then
        error (exp.A.st_data) ("context " ^ PP.pp_chantp_list ldelta ^ " must have only one channel")
      else if y <> ty then
        E.error_unknown_var_ctx (y) (exp.A.st_data)
      (* "subtype is sufficient with subsync types" *)
      else if eqtp env a c
      then ()
      else error (exp.A.st_data) ("left type " ^ PP.pp_proto env a ^ " not equal to right type " ^
                                  PP.pp_proto env c)
    end
  | A.Spawn(a,x,f,ids,ps,xs,q) ->
    begin
      match A.lookup_expdec env f with
        None -> E.error_undeclared (f) (exp.A.st_data)
      | Some (ctx,lpot,(x',a'),mdef) ->
        let (_s,_x,mx) = x in
        if check_tp x delta || checktp x [zc]
        then error (exp.A.st_data) ("variable " ^ name_of x ^ " is not fresh")
        else if not (ge pot lpot)
        then error (exp.A.st_data) ("insufficient potential to spawn: " ^ pp_lt pot lpot)
        else if not (eq_mode x x')
        then E.error_mode_mismatch (x, x') (exp.A.st_data)
        else if not (eqmode mx mdef)
        then error (exp.A.st_data) ("mode mismatch: expected " ^ PP.pp_mode mdef ^ " at declaration, found: " ^ PP.pp_chan x)
        else if not (mode_spawn mdef mode)
        then error (exp.A.st_data) ("cannot spawn at mode " ^ PP.pp_mode mdef ^ " when current mode is " ^ PP.pp_mode mode)
        else
          let ctx = join ctx in
          let delta' = match_ctx env ctx xs delta (List.length ctx) (List.length xs) (exp.A.st_data) in
          check_exp' trace env (add_chan env (x,a') delta') (minus pot lpot) q zc ext mode
    end
  | A.ExpName(x,f,ids,ps,xs) ->
    begin
      match A.lookup_expdec env f with
        None -> E.error_undeclared (f) (exp.A.st_data)
      | Some (ctx,lpot,(x',a'),mdef) ->
        let (_s,_x,mx) = x in
        if not (eq pot lpot)
        then error (exp.A.st_data) ("potential mismatch for tail call: " ^ pp_uneq pot lpot)
        else if not (eq_mode x x')
        then E.error_mode_mismatch (x, x') (exp.A.st_data)
        else if not (eqmode mx mdef)
        then error (exp.A.st_data) ("mode mismatch: expected " ^ PP.pp_mode mdef ^ " at declaration, found: " ^ PP.pp_chan x)
        else if not (mode_spawn mdef mode)
        then error (exp.A.st_data) ("cannot tail call at mode " ^ PP.pp_mode mdef ^ " when current mode is " ^ PP.pp_mode mode)
        else
          let (z,c) = zc in
          if not (eq_name x z)
          then E.error_unknown_var_right (x) (exp.A.st_data)
          else if not (eq_mode x z)
          then E.error_mode_mismatch (x, z) (exp.A.st_data)
          (* "subtype is sufficient with subsync types" *)
          else if not (subtp env a' c)
          then error (exp.A.st_data) ("type mismatch on right, expected: " ^ PP.pp_tp_compact env a' ^
                                      ", found: " ^ PP.pp_tp_compact env c)
          else
            let ctx = join ctx in
            let delta' = match_ctx env ctx xs delta (List.length ctx) (List.length xs) (exp.A.st_data) in
            if List.length delta'.linear <> 0
            then error (exp.A.st_data) ("unconsumed channel(s) from linear context: " ^ PP.pp_lsctx env delta'.linear)
            else ()
    end
  | A.Lab(x,k,p) ->
    begin
      if not (check_ltp x delta)
      then
        if not (checktp x [zc])
        then E.error_unknown_var (x) (exp.A.st_data)
        else (* the type c of z must be internal choice *)
          let (z,c) = zc in
          if not (eq_mode x z)
          then E.error_mode_mismatch (x, z) (exp.A.st_data)
          else if not (mode_lin x)
          then E.error_mode_shared_comm (x) (exp.A.st_data)
          else
            match c with
              A.TpName(v) -> check_exp' trace env delta pot exp (z,A.expd_tp env v) ext mode
            | A.Plus(choices) ->
              begin
                match A.lookup_choice choices k with
                  None -> E.error_label_invalid env (k,c,z) (exp.A.st_data)
                | Some ck -> check_exp' trace env delta pot p (z,ck) ext mode
              end
            | A.With _ | A.One
            | A.Tensor _ | A.Lolli _
            | A.PayPot _ | A.GetPot _
            | A.Up _ | A.Down _
            | A.FArrow _ | A.FProduct _
            | A.FMap _ | A.STMap _
            | A.Coin ->
              error (exp.A.st_data) ("invalid type of " ^ PP.pp_chan z ^
                                     ", expected internal choice, found: " ^ PP.pp_tp_compact env c)
      else (* the type a of x must be external choice *)
        let a = find_ltp x delta (exp.A.st_data) in
        match a with
          A.TpName(v) -> check_exp' trace env (update_tp env x (A.expd_tp env v) delta) pot exp zc ext mode
        | A.With(choices) ->
          begin
            match A.lookup_choice choices k with
              None -> E.error_label_invalid env (k,a,x) (exp.A.st_data)
            | Some ak -> check_exp' trace env (update_tp env x ak delta) pot p zc ext mode
          end
        | A.Plus _ | A.One
        | A.Tensor _ | A.Lolli _
        | A.PayPot _ | A.GetPot _
        | A.Up _ | A.Down _
        | A.FArrow _ | A.FProduct _
        | A.FMap _ | A.STMap _
        | A.Coin ->
          error (exp.A.st_data) ("invalid type of " ^ PP.pp_chan x ^
                                 ", expected external choice, found: " ^ PP.pp_tp_compact env a)
    end
  | A.Case(x,branches) ->
    begin
      if not (check_ltp x delta)
      then
        if not (checktp x [zc])
        then E.error_unknown_var (x) (exp.A.st_data)
        else (* the type c of z must be external choice *)
          let (z,c) = zc in
          if not (eq_mode x z)
          then E.error_mode_mismatch (x, z) (exp.A.st_data)
          else if not (mode_lin x)
          then E.error_mode_shared_comm (x) (exp.A.st_data)
          else
            match c with
              A.TpName(v) -> check_exp' trace env delta pot exp (z,A.expd_tp env v) ext mode
            | A.With(choices) -> check_branchesR trace env delta pot branches z choices (exp.A.st_data) mode
            | A.Plus _ | A.One
            | A.Tensor _ | A.Lolli _
            | A.PayPot _ | A.GetPot _
            | A.Up _ | A.Down _
            | A.FArrow _ | A.FProduct _
            | A.FMap _ | A.STMap _
            | A.Coin ->
              error (exp.A.st_data) ("invalid type of " ^ PP.pp_chan z ^
                                     ", expected external choice, found: " ^ PP.pp_tp_compact env c)
      else (* the type a of x must be internal choice *)
        let a = find_ltp x delta (exp.A.st_data) in
        match a with
          A.TpName(v) -> check_exp' trace env (update_tp env x (A.expd_tp env v) delta) pot exp zc ext mode
        | A.Plus(choices) -> check_branchesL trace env delta x choices pot branches zc (exp.A.st_data) mode
        | A.With _ | A.One
        | A.Tensor _ | A.Lolli _
        | A.PayPot _ | A.GetPot _
        | A.Up _ | A.Down _
        | A.FArrow _ | A.FProduct _
        | A.FMap _ | A.STMap _
        | A.Coin ->
          error (exp.A.st_data) ("invalid type of " ^ PP.pp_chan x ^
                                 ", expected internal choice, found: " ^ PP.pp_tp_compact env a)
    end
  | A.Send(x,w,p) ->
    begin
      if not (check_tp w delta)
      then E.error_unknown_var_ctx (w) (exp.A.st_data)
      else if check_ltp w delta
      then
        begin
          let a' = find_ltp w delta (exp.A.st_data) in
          if not (check_tp x delta)
          then
            if not (checktp x [zc])
            then E.error_unknown_var (x) (exp.A.st_data)
            else (* the type c of z must be tensor *)
              let (z,c) = zc in
              if not (eq_mode x z)
              then E.error_mode_mismatch (x, z) (exp.A.st_data)
              else if not (mode_lin x)
              then E.error_mode_shared_comm (x) (exp.A.st_data)
              else
                match c with
                  A.TpName(v) -> check_exp' trace env delta pot exp (z,A.expd_tp env v) ext mode
                | A.Tensor(a,b,m) ->
                  let (_sw,_w,mw) = w in
                  if not (eqmode m mw)
                  then error (exp.A.st_data) ("mode mismatch, expected at tensor: " ^ PP.pp_mode m ^ ", found: " ^ PP.pp_chan w)
                  (* "subtype is sufficient with subsync types" *)
                  else if not (subtp env a' a)
                  then error (exp.A.st_data) ("type mismatch: type of " ^ PP.pp_chan w ^
                                              ", expected: " ^ PP.pp_tp_compact env a ^
                                              ", found: " ^ PP.pp_tp_compact env a')
                  else check_exp' trace env (remove_tp w delta) pot p (z,b) ext mode
                | A.Plus _ | A.With _
                | A.One | A.Lolli _
                | A.PayPot _ | A.GetPot _
                | A.Up _ | A.Down _
                | A.FArrow _ | A.FProduct _
                | A.FMap _ | A.STMap _
                | A.Coin ->
                  error (exp.A.st_data) ("invalid type of " ^ PP.pp_chan x ^
                                         ", expected tensor, found: " ^ PP.pp_tp_compact env c)
          else (* the type a of x must be lolli *)
            let d = find_ltp x delta (exp.A.st_data) in
            match d with
              A.TpName(v) -> check_exp' trace env (update_tp env x (A.expd_tp env v) delta) pot exp zc ext mode
            | A.Lolli(a,b,m) ->
              let (_sw,_w,mw) = w in
              if not (eqmode m mw)
              then error (exp.A.st_data) ("mode mismatch, expected at lolli: " ^ PP.pp_mode m ^ ", found: " ^ PP.pp_chan w)
              (* "subtype is sufficient with subsync types" *)
              else if not (subtp env a' a)
              then error (exp.A.st_data) ("type mismatch: type of " ^ PP.pp_chan w ^
                                          ", expected: " ^ PP.pp_tp_compact env a ^
                                          ", found: " ^ PP.pp_tp_compact env a')
              else check_exp' trace env (update_tp env x b (remove_tp w delta)) pot p zc ext mode
            | A.Plus _ | A.With _
            | A.One | A.Tensor _
            | A.PayPot _ | A.GetPot _
            | A.Up _ | A.Down _
            | A.FArrow _ | A.FProduct _
            | A.FMap _ | A.STMap _
            | A.Coin ->
              error (exp.A.st_data) ("invalid type of " ^ PP.pp_chan x ^
                                     ", expected lolli, found: " ^ PP.pp_tp_compact env d)
        end
      else
        begin
          let a' = find_stp w delta (exp.A.st_data) in
          if not (check_tp x delta)
          then
            if not (checktp x [zc])
            then E.error_unknown_var (x) (exp.A.st_data)
            else (* the type c of z must be tensor *)
              let (z,c) = zc in
              if not (eq_mode x z)
              then E.error_mode_mismatch (x, z) (exp.A.st_data)
              else if not (mode_lin x)
              then E.error_mode_shared_comm (x) (exp.A.st_data)
              else
                match c with
                  A.TpName(v) -> check_exp' trace env delta pot exp (z,A.expd_tp env v) ext mode
                | A.Tensor(a,b,m) ->
                  let (_sw,_w,mw) = w in
                  if not (eqmode m mw)
                  then error (exp.A.st_data) ("mode mismatch, expected at tensor: " ^ PP.pp_mode m ^ ", found: " ^ PP.pp_chan w)
                  (* "subtype is sufficient with subsync types" *)
                  else if not (subtp env a' a)
                  then error (exp.A.st_data) ("type mismatch: type of " ^ PP.pp_chan w ^
                                              ", expected: " ^ PP.pp_tp_compact env a ^
                                              ", found: " ^ PP.pp_tp_compact env a')
                  else check_exp' trace env delta pot p (z,b) ext mode
                | A.Plus _ | A.With _
                | A.One | A.Lolli _
                | A.PayPot _ | A.GetPot _
                | A.Up _ | A.Down _
                | A.FArrow _ | A.FProduct _
                | A.FMap _ | A.STMap _
                | A.Coin ->
                  error (exp.A.st_data) ("invalid type of " ^ PP.pp_chan x ^
                                         ", expected tensor, found: " ^ PP.pp_tp_compact env c)
          else (* the type a of x must be lolli *)
            let d = find_ltp x delta (exp.A.st_data) in
            match d with
              A.TpName(v) -> check_exp' trace env (update_tp env x (A.expd_tp env v) delta) pot exp zc ext mode
            | A.Lolli(a,b,m) ->
              let (_sw,_w,mw) = w in
              if not (eqmode m mw)
              then error (exp.A.st_data) ("mode mismatch, expected at lolli: " ^ PP.pp_mode m ^ ", found: " ^ PP.pp_chan w)
              (* "subtype is sufficient with subsync types" *)
              else if not (subtp env a' a)
              then error (exp.A.st_data) ("type mismatch: type of " ^ PP.pp_chan w ^
                                          ", expected: " ^ PP.pp_tp_compact env a ^
                                          ", found: " ^ PP.pp_tp_compact env a')
              else check_exp' trace env (update_tp env x b delta) pot p zc ext mode
            | A.Plus _ | A.With _
            | A.One | A.Tensor _
            | A.PayPot _ | A.GetPot _
            | A.Up _ | A.Down _
            | A.FArrow _ | A.FProduct _
            | A.FMap _ | A.STMap _
            | A.Coin ->
              error (exp.A.st_data) ("invalid type of " ^ PP.pp_chan x ^
                                     ", expected lolli, found: " ^ PP.pp_tp_compact env d)
        end
    end
  | A.Recv(x,y,p) ->
    begin
      if check_tp y delta || checktp y [zc]
      then error (exp.A.st_data) ("variable " ^ name_of y ^ " is not fresh")
      else
      if not (check_ltp x delta)
      then
        if not (checktp x [zc])
        then E.error_unknown_var (x) (exp.A.st_data)
        else (* the type c of z must be lolli *)
          let (z,c) = zc in
          if not (eq_mode x z)
          then E.error_mode_mismatch (x, z) (exp.A.st_data)
          else if not (mode_lin x)
          then E.error_mode_shared_comm (x) (exp.A.st_data)
          else
            match c with
              A.TpName(v) -> check_exp' trace env delta pot exp (z,A.expd_tp env v) ext mode
            | A.Lolli(a,b,m) ->
              let (_sy,_y,my) = y in
              if not (eqmode m my)
              then error (exp.A.st_data) ("mode mismatch, expected at lolli: " ^ PP.pp_mode m ^ ", found: " ^ PP.pp_chan y)
              else if not (mode_recv m mode)
              then error (exp.A.st_data) ("cannot receive at mode " ^ PP.pp_mode m ^ " when current mode is " ^ PP.pp_mode mode)
              else check_exp' trace env (add_chan env (y,a) delta) pot p (z,b) ext mode
            | A.Plus _ | A.With _
            | A.One | A.Tensor _
            | A.PayPot _ | A.GetPot _
            | A.Up _ | A.Down _
            | A.FArrow _ | A.FProduct _
            | A.FMap _ | A.STMap _
            | A.Coin ->
              error (exp.A.st_data) ("invalid type of " ^ PP.pp_chan x ^
                                     ", expected lolli, found: " ^ PP.pp_tp_compact env c)
      else (* the type a of x must be tensor *)
        let d = find_ltp x delta (exp.A.st_data) in
        match d with
          A.TpName(v) -> check_exp' trace env (update_tp env x (A.expd_tp env v) delta) pot exp zc ext mode
        | A.Tensor(a,b,m) ->
          let (_sy,_y,my) = y in
          if not (eqmode m my)
          then error (exp.A.st_data) ("mode mismatch, expected at tensor: " ^ PP.pp_mode m ^ ", found: " ^ PP.pp_chan y)
          else if not (mode_recv m mode)
          then error (exp.A.st_data) ("cannot receive at mode " ^ PP.pp_mode m ^ " when current mode is " ^ PP.pp_mode mode)
          else check_exp' trace env (add_chan env (y,a) (update_tp env x b delta)) pot p zc ext mode
        | A.Plus _ | A.With _
        | A.One | A.Lolli _
        | A.PayPot _ | A.GetPot _
        | A.Up _ | A.Down _
        | A.FArrow _ | A.FProduct _
        | A.FMap _ | A.STMap _
        | A.Coin ->
          error (exp.A.st_data) ("invalid type of " ^ PP.pp_chan x ^
                                 ", expected tensor, found: " ^ PP.pp_tp_compact env d)
    end
  | A.Close(x) ->
    begin
      let {A.shared = _sdelta ; A.linear = ldelta ; A.ordered = _odelta} = delta in
      if List.length ldelta > 0
      then error (exp.A.st_data) ("linear context " ^ PP.pp_lsctx env ldelta ^ " not empty")
      else if not (checktp x [zc])
      then E.error_unknown_var (x) (exp.A.st_data)
      else if not (eq pot zero)
      then error (exp.A.st_data) ("unconsumed potential: " ^ pp_uneq pot zero)
      else
        let (z,c) = zc in
        if not (eq_mode x z)
        then E.error_mode_mismatch (x, z) (exp.A.st_data)
        else if not (mode_lin x)
        then E.error_mode_shared_comm (x) (exp.A.st_data)
        else
          (* "subtype is sufficient with subsync types" *)
        if not (subtp env c A.One)
        then error (exp.A.st_data) ("type mismatch: type of " ^ PP.pp_chan x ^ ", expected: 1, " ^
                                    "found: " ^ PP.pp_tp_compact env c)
        else ()
    end
  | A.Wait(x,p) ->
    begin
      if not (check_ltp x delta)
      then E.error_unknown_var (x) (exp.A.st_data)
      else
        let a = find_ltp x delta (exp.A.st_data) in
        (* "subtype is sufficient with subsync types" *)
        if not (subtp env a A.One)
        then error (exp.A.st_data) ("type mismatch: type of " ^ PP.pp_chan x ^ ", expected: 1, " ^
                                    " found: " ^ PP.pp_tp_compact env a)
        else check_exp' trace env (remove_tp x delta) pot p zc ext mode
    end
  | A.Abort -> ()
  | A.Print(l,args,p) ->
    begin
      let () = check_printable_list delta (exp.A.st_data) l args (List.length (filter_args l)) (List.length args) in
      check_exp' trace env delta pot p zc ext mode
    end

and check_branchesR trace env delta pot branches z choices ext mode = match branches, choices with
    (l1,p)::branches', (l2,c)::choices' ->
    begin
        if trace then print_string ("| " ^ l1 ^ " => \n") else ()
        ; if l1 = l2 then () else E.error_label_mismatch (l1, l2) ext
        ; check_exp' trace env delta pot p (z,c) (p.A.st_data) mode
        ; check_branchesR trace env delta pot branches' z choices' ext mode
    end
    | [], [] -> ()
    | (l,_p)::_branches', [] ->
        E.error_label_missing_alt (l) ext
    | [], (l,_c)::_choices' ->
        E.error_label_missing_branch (l) ext

and check_branchesL trace env delta x choices pot branches zc ext mode = match choices, branches with
    (l1,a)::choices', (l2,p)::branches' ->
    begin
        if trace then print_string ("| " ^ l1 ^ " => \n") else ()
        ; if l1 = l2 then () else E.error_label_mismatch (l1, l2) ext
        ; check_exp' trace env (update_tp env x a delta) pot p zc (p.A.st_data) mode
        ; check_branchesL trace env delta x choices' pot branches' zc ext mode
    end
    | [], [] -> ()
    | [], (l,_p)::_branches' ->
        E.error_label_missing_alt (l) ext
    | (l,_a)::_choices', [] ->
        E.error_label_missing_branch (l) ext;;

      (* let rec link_tps env state_channels args odelta ext =
           match args, odelta with
               [], [] -> ()
             | (A.FArg e)::_args', (A.Functional _)::_odelta' ->
                 linkerror ext ("functional arguments not allowed in executing process: " ^ PP.pp_fexp env 0 e)
             | (A.FArg e)::_args', (A.STyped _)::_odelta' ->
                 linkerror ext ("expected session-typed argument, found functional argument: " ^ PP.pp_fexp env 0 e)
             | (A.STArg c)::_args', (A.Functional _)::_odelta' ->
                 linkerror ext ("expected functional argument, found channel: " ^ PP.pp_chan c)
             | [], _hd::_tl -> raise UnknownTypeError
             | _hd::_tl, [] -> raise UnknownTypeError
             | (A.STArg c)::args', (A.STyped(_x,sigt))::odelta' ->
                 match M.find state_channels c with
                     None -> raise UnknownTypeError
                   | Some t ->
                       if not (subtp env t sigt)
                       then linkerror ext ("type mismatch of " ^ PP.pp_chan c ^
                                           " expected: " ^ PP.pp_tp_compact env sigt ^
                                           ", found: " ^ PP.pp_tp_compact env t)
                       else link_tps env state_channels args' odelta' ext;;

         let rec consistent_mode f delta odelta ext =
           match odelta with
               [] -> ()
             | (A.Functional _)::odelta' -> consistent_mode f delta odelta' ext
             | (A.STyped (x,_t))::odelta' ->
                 let (y,_t) = find_tp x delta in
                 if not (eq_mode x y)
                 then E.error_mode_mismatch (x, y) ext
                 else consistent_mode f delta odelta' ext;;

         let rec mode_P_list delta = match delta with
             [] -> true
           | (x,_t)::delta' -> if not (mode_P x) then false else mode_P_list delta';;

         let pure env f delta x ext =
           let {A.shared = sdelta ; A.linear = ldelta ; A.ordered = odelta} = delta in
           let () = consistent_mode f delta odelta ext in
           if not (mode_P x)
           then error ext ("asset process " ^ f ^ " has offered channel at mode " ^ PP.pp_chan x)
           else if List.length sdelta > 0
           then error ext ("asset process " ^ f ^ " has non-empty shared context: " ^ PP.pp_lsctx env sdelta)
           else if not (mode_P_list ldelta)
           then error ext ("asset process " ^ f ^ " has non-pure linear context: " ^ PP.pp_lsctx env ldelta)
           else ();;

         let rec mode_S_list delta = match delta with
             [] -> true
           | (x,_t)::delta' -> if not (mode_S x) then false else mode_S_list delta';;

         let shared env f delta x ext =
           let {A.shared = sdelta ; A.linear = ldelta ; A.ordered = odelta} = delta in
           let () = consistent_mode f delta odelta ext in
           if not (mode_S x)
           then error ext ("shared process " ^ f ^ " has offered channel at mode " ^ PP.pp_chan x)
           else if not (mode_S_list sdelta)
           then error ext ("shared process " ^ f ^ " has non-shared context: " ^ PP.pp_lsctx env sdelta)
           else if not (mode_P_list ldelta)
           then error ext ("shared process " ^ f ^ " has non-pure linear context: " ^ PP.pp_lsctx env ldelta)
           else ();;

         let rec mode_lin_list delta = match delta with
             [] -> true
           | (x,_t)::delta' -> if not (mode_lin x) then false else mode_lin_list delta';;

         let transaction env f delta x ext =
           let {A.shared = sdelta ; A.linear = ldelta ; A.ordered = odelta} = delta in
           let () = consistent_mode f delta odelta ext in
           if not (mode_T x)
           then error ext ("transaction process " ^ f ^ " has offered channel at mode " ^ PP.pp_chan x)
           else if not (mode_S_list sdelta)
           then error ext ("transaction process " ^ f ^ " has shared context not at shared mode: " ^ PP.pp_lsctx env sdelta)
           else if not (mode_lin_list ldelta)
           then error ext ("transaction process " ^ f ^ " has linear context not at linear mode: " ^ PP.pp_lsctx env ldelta)
           else ();; *)
