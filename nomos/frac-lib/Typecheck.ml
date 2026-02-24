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
  then print_string ("comparing " ^ PP.pp_proto env a ^ " and " ^ PP.pp_proto env a' ^ "\n")
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

let has_chan c ctx =
  let {A.idnames = _idnames ; A.permnames = _permnames ; A.owned = _owned ; A.locked = ldelta ; A.linear = delta} = ctx in
  List.mem_assoc c ldelta || List.mem_assoc c delta

let remove_chan c ctx =
  let delta = ctx.A.linear in
  { ctx with A.linear = List.remove_assoc c delta }

let add_chan env (x,t) ctx =
  { ctx with A.linear = (x,t)::ctx.A.linear }

let update_tp env x t ctx =
  let ctx = remove_chan x ctx in
  { ctx with A.linear = (x,t)::ctx.A.linear }

let find_tp c ctx ext =
  if List.mem_assoc c ctx.A.locked then
    E.error_use_locked c ext
  else
    match List.assoc_opt c ctx.A.linear with
    | Some (res) -> res
    | None -> error ext ("unknown channel " ^ c)

let rec match_ctx env sig_delta ctx xs sig_len len ext =
  match sig_delta, xs with
  | (y', (a',p',id'))::sig_ctx', y::xs' ->
    begin
      let (a,p,id) = find_tp y ctx ext in
      if not (A.perm_eq p p') then
        error ext ("permission mismatch: permission " ^ PP.pp_perm p ^
                   " of " ^ y ^ " does not match permission in declaration: " ^ PP.pp_perm p')
      else if not (id = id') then
        error ext ("id mismatch: id " ^ id ^ " of " ^ y ^ " does not match id in declaration: " ^ id')
      else if not (eqtp env a a') then
        error ext ("type mismatch: type of " ^ y ^ " : " ^ PP.pp_proto env a ^
                   " does not match type in declaration: " ^ PP.pp_proto env a')
      else
        match_ctx env sig_ctx' (remove_chan y ctx) xs' sig_len len ext
    end
  | [], [] -> ctx
  | _, _ -> error ext ("process defined with " ^ string_of_int sig_len ^
                       " arguments but called with " ^ string_of_int len ^ " arguments")

let rec check_printable_list ctx ext plist arglist plen arglen =
  match plist, arglist with
    [], [] -> ()
  | A.Word(_)::ps, _ -> check_printable_list ctx ext ps arglist plen arglen
  | A.PNewline::ps, _ -> check_printable_list ctx ext ps arglist plen arglen
  | A.PChan::ps, arg::args ->
    if not (has_chan arg ctx)
    then error ext ("unknown or duplicate variable: " ^ arg)
    else
      check_printable_list ctx ext ps args plen arglen
  | _, _ ->
    error ext ("print string expects " ^ string_of_int plen ^
               " arguments but called with " ^ string_of_int arglen ^ " arguments")

let is_argtype p = match p with
    A.Word _ | A.PNewline -> false
  | A.PChan -> true

let filter_args l = List.filter (fun p -> is_argtype p) l

let is_tpdef env a = match A.lookup_tp env a with None -> false | Some _ -> true
let is_expdecdef env f = match A.lookup_expdef env f with None -> false | Some _ -> true

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

let check_perm p ctx =
  match p with
  | A.Owned -> true
  | A.Fractional p -> A.StringMap.for_all (fun v x -> List.mem v ctx.A.permnames) p

let check_id id ctx =
  List.mem id ctx.A.idnames

let rec checkexp trace env ctx p zc ext cont = check_exp' trace env ctx p zc ext cont

and check_exp' trace env ctx p zc (ext:A.ext) cont =
begin
    if trace
    then print_string (PP.pp_exp_prefix (p.A.st_structure) ^ " : "
                        ^ PP.pp_tpj_compact env ctx zc ^ "\n")
    else ()
end
; check_exp trace env ctx p zc ext cont


(* judgmental constructs: id, cut, spawn, call *)
and check_exp trace env ctx exp zc ext cont = match (exp.A.st_structure) with
    A.Fwd(x,y) ->
    begin
      let {A.idnames = idnames ; A.permnames = permnames ; A.owned = owned ; A.locked = ldelta ; A.linear = delta} = ctx in
      let () =
        if List.length owned > 0 then
          error (exp.A.st_data) ("forward with owned ids " ^ PP.pp_channames owned)
        else if List.length ldelta > 0 then
          error (exp.A.st_data) ("forward with locked channels " ^ PP.pp_chantp_list ldelta)
        else ()
      in
      let z = chan_of zc in
      let () =
        if x <> z then
          error (exp.A.st_data) ("forward to " ^ x ^ " instead of expected " ^ z)
        else ()
      in
      let c = tp_of zc in
      let (ty, (a, p, id)) = List.hd delta in
      if List.length delta <> 1 then
        error (exp.A.st_data) ("context " ^ PP.pp_chantp_list delta ^ " must have only one channel")
      else if y <> ty then
        E.error_unknown_var_ctx (y) (exp.A.st_data)
      (* "subtype is sufficient with subsync types" (not using this rn) *)
      else if not (eqtp env a c) then
        error (exp.A.st_data) ("left type " ^ PP.pp_proto env a ^ " not equal to right type " ^
                                  PP.pp_proto env c)
      else match p with
        | A.Owned -> ()
        | _ -> error (exp.A.st_data) ("forward non-owned channel " ^ y)
    end
  | A.Spawn(id,x,f,ids,ps,xs,q) ->
    begin
      match A.lookup_expdec env f with
        None -> E.error_undeclared (f) (exp.A.st_data)
      | Some (ids',ps',delta',(x',a')) ->
        if has_chan x ctx || x = (fst zc) then
          error (exp.A.st_data) ("variable " ^ x ^ " is not fresh")
        else if List.mem id ctx.A.idnames then
          error (exp.A.st_data) ("id " ^ id ^ " is not fresh")
        else if List.length ids <> List.length ids' then
          error (exp.A.st_data) ("mismatched number of ids: expected " ^ PP.pp_channames ids' ^ ", got " ^ PP.pp_channames ids)
        else if List.length ps <> List.length ps' then
          error (exp.A.st_data) ("mismatched number of perms: expected " ^ PP.pp_channames ps' ^ ", got " ^ PP.pp_perms ps)
        else
          let () = List.iter(fun p -> if not (check_perm p ctx) then error (exp.A.st_data) ("invalid permission " ^ PP.pp_perm p) else ()) ps in
          let () = List.iter(fun id -> if not (check_id id ctx) then error (exp.A.st_data) ("unknown id " ^ id) else ()) ids in
          (* update signature with provided substitution *)
          let delta' = List.map (fun (x,t) -> (x, A.stype_subst_perms ps ps' (A.stype_subst_ids ids ids' t))) delta' in
          let a' = A.proto_subst_perms ps ps' (A.proto_subst_ids ids ids' a') in
          let ctx' = match_ctx env delta' ctx xs (List.length delta') (List.length xs) (exp.A.st_data) in
          let ctx' = { ctx' with A.idnames = id::ctx'.A.idnames ; A.linear = (x, (a', Owned, id))::ctx'.A.linear } in
          check_exp' trace env ctx' q zc ext cont
    end
  | A.ExpName(x,f,ids,ps,xs) ->
    begin
      match A.lookup_expdec env f with
        None -> E.error_undeclared (f) (exp.A.st_data)
      | Some (ids',ps',delta',(x',a')) ->
        if List.length ids <> List.length ids' then
          error (exp.A.st_data) ("mismatched number of ids: expected " ^ PP.pp_channames ids' ^ ", got " ^ PP.pp_channames ids)
        else if List.length ps <> List.length ps' then
          error (exp.A.st_data) ("mismatched number of perms: expected " ^ PP.pp_channames ps' ^ ", got " ^ PP.pp_perms ps)
        else
          let () = List.iter(fun p -> if not (check_perm p ctx) then error (exp.A.st_data) ("invalid permission " ^ PP.pp_perm p) else ()) ps in
          let () = List.iter(fun id -> if not (check_id id ctx) then error (exp.A.st_data) ("unknown id " ^ id) else ()) ids in
          (* update signature with provided substitution *)
          let delta' = List.map (fun (x,t) -> (x, A.stype_subst_perms ps ps' (A.stype_subst_ids ids ids' t))) delta' in
          let a' = A.proto_subst_perms ps ps' (A.proto_subst_ids ids ids' a') in
          let ctx' = match_ctx env delta' ctx xs (List.length delta') (List.length xs) (exp.A.st_data) in
          let {A.idnames = idnames ; A.permnames = permnames ; A.owned = owned ; A.locked = ldelta ; A.linear = delta} = ctx' in
          let () =
            if List.length owned > 0 then
              error (exp.A.st_data) ("tail-call with owned ids " ^ PP.pp_channames owned)
            else if List.length ldelta > 0 then
              error (exp.A.st_data) ("tail-call with locked channels " ^ PP.pp_chantp_list ldelta)
            else ()
          in
          let z = chan_of zc in
          let () =
            if x <> z then
              error (exp.A.st_data) ("forward to " ^ x ^ " instead of expected " ^ z)
            else ()
          in
          let c = tp_of zc in
          if List.length delta > 0 then
            error (exp.A.st_data) ("tail-call with extra channels: " ^ PP.pp_chantp_list delta)
            (* "subtype is sufficient with subsync types" (not using this rn) *)
          else if not (eqtp env a' c) then
            error (exp.A.st_data) ("left type " ^ PP.pp_proto env a' ^ " not equal to right type " ^
                                   PP.pp_proto env c)
          else ()
    end
  | A.Lab(x,k,cont_p) ->
    begin
      if not (has_chan x ctx)
      then
        let (z,c) = zc in
        if x <> z then
          E.error_unknown_var (x) (exp.A.st_data)
        else (* the type c of z must be internal choice *)
          match c with
            A.TpName(v) -> check_exp' trace env ctx exp (z,A.expd_tp env v) ext cont
          | A.Plus(choices) ->
            begin
              match A.lookup_choice choices k with
                None -> E.error_label_invalid env (k,c,z) (exp.A.st_data)
              | Some ck -> check_exp' trace env ctx cont_p (z,ck) ext cont
              end
            | _ ->
              error (exp.A.st_data) ("invalid type of " ^ z ^
                                     ", expected internal choice, found: " ^ PP.pp_proto env c)
      else (* the type a of x must be external choice *)
        let (a,p,id) = find_tp x ctx (exp.A.st_data) in
        match a with
          A.TpName(v) -> check_exp' trace env (update_tp env x ((A.expd_tp env v),p,id) ctx) exp zc ext cont
        | A.With(choices) ->
          begin
            match A.lookup_choice choices k with
              None -> E.error_label_invalid env (k,a,x) (exp.A.st_data)
            | Some ak -> check_exp' trace env (update_tp env x (ak,p,id) ctx) cont_p zc ext cont
          end
        | _ ->
          error (exp.A.st_data) ("invalid type of " ^ x ^
                                 ", expected external choice, found: " ^ PP.pp_proto env a)
    end
  | A.Case(x,branches) ->
    begin
      if not (has_chan x ctx)
      then
        let (z,c) = zc in
        if x <> z then
          E.error_unknown_var (x) (exp.A.st_data)
        else (* the type c of z must be external choice *)
            match c with
              A.TpName(v) -> check_exp' trace env ctx exp (z,A.expd_tp env v) ext cont
            | A.With(choices) -> check_branchesR trace env ctx branches z choices (exp.A.st_data) cont
            | _ ->
              error (exp.A.st_data) ("invalid type of " ^ z ^
                                     ", expected external choice, found: " ^ PP.pp_proto env c)
      else (* the type a of x must be internal choice *)
        let (a,p,id) = find_tp x ctx (exp.A.st_data) in
        match a with
          A.TpName(v) -> check_exp' trace env (update_tp env x ((A.expd_tp env v),p,id) ctx) exp zc ext cont
        | A.Plus(choices) -> check_branchesL trace env ctx x choices branches zc (exp.A.st_data) cont
        | _ ->
          error (exp.A.st_data) ("invalid type of " ^ x ^
                                 ", expected internal choice, found: " ^ PP.pp_proto env a)
    end
  | A.Send(x,w,cont_p) ->
    begin
      if not (has_chan w ctx) then
        E.error_unknown_var_ctx (w) (exp.A.st_data)
      else
          let (a',p',id') = find_tp w ctx (exp.A.st_data) in
          if not (has_chan x ctx)
          then
            let (z,c) = zc in
            if x <> z then
              E.error_unknown_var (x) (exp.A.st_data)
            else (* the type c of z must be tensor *)
                match c with
                  A.TpName(v) -> check_exp' trace env ctx exp (z,A.expd_tp env v) ext cont
                | A.Tensor((a,p,id),b) ->
                  (* "subtype is sufficient with subsync types" *)
                  if not (eqtp env a' a) then
                    error (exp.A.st_data) ("type mismatch: type of " ^ w ^
                                              ", expected: " ^ PP.pp_proto env a ^
                                              ", found: " ^ PP.pp_proto env a')
                  else if not (A.perm_eq p' p) then
                    error (exp.A.st_data) ("permission mismatch: permission of " ^ w ^
                                           ", expected: " ^ PP.pp_perm p ^
                                           ", found: " ^ PP.pp_perm p')
                  else if id' <> id then
                    error (exp.A.st_data) ("id mismatch: id of " ^ w ^
                                           ", expected: " ^ id ^ ", found: " ^ id')
                  else check_exp' trace env (remove_chan w ctx) cont_p (z,b) ext cont
                | _ ->
                  error (exp.A.st_data) ("invalid type of " ^ x ^
                                         ", expected tensor, found: " ^ PP.pp_proto env c)
          else (* the type d of x must be lolli *)
            let (d,q,idx) = find_tp x ctx (exp.A.st_data) in
            match d with
              A.TpName(v) -> check_exp' trace env (update_tp env x ((A.expd_tp env v),q,idx) ctx) exp zc ext cont
            | A.Lolli((a,p,id),b) ->
              (* "subtype is sufficient with subsync types" *)
              if not (eqtp env a' a) then
                error (exp.A.st_data) ("type mismatch: type of " ^ w ^
                                          ", expected: " ^ PP.pp_proto env a ^
                                          ", found: " ^ PP.pp_proto env a')
              else if not (A.perm_eq p' (A.perm_mult p q)) then
                error (exp.A.st_data) ("permission mismatch: permission of " ^ w ^
                                       ", expected: " ^ PP.pp_perm p ^
                                       ", found: " ^ PP.pp_perm p')
              else if id' <> id then
                error (exp.A.st_data) ("id mismatch: id of " ^ w ^
                                       ", expected: " ^ id ^ ", found: " ^ id')
              else check_exp' trace env (update_tp env x (b,q,idx) (remove_chan w ctx)) cont_p zc ext cont
            | _ ->
              error (exp.A.st_data) ("invalid type of " ^ x ^
                                     ", expected lolli, found: " ^ PP.pp_proto env d)
    end
  | A.Recv(x,y,cont_p) ->
    begin
      let (z,c) = zc in
      if has_chan y ctx || y = z then
        error (exp.A.st_data) ("variable " ^ y ^ " is not fresh")
      else
      if not (has_chan x ctx)
      then
        if x <> z then
          E.error_unknown_var (x) (exp.A.st_data)
        else (* the type c of z must be lolli *)
            match c with
              A.TpName(v) -> check_exp' trace env ctx exp (z,A.expd_tp env v) ext cont
            | A.Lolli(a,b) ->
              check_exp' trace env (add_chan env (y,a) ctx) cont_p (z,b) ext cont
            | _ ->
              error (exp.A.st_data) ("invalid type of " ^ x ^
                                     ", expected lolli, found: " ^ PP.pp_proto env c)
      else (* the type a of x must be tensor *)
        let (d,q,idx) = find_tp x ctx (exp.A.st_data) in
        match d with
          A.TpName(v) -> check_exp' trace env (update_tp env x ((A.expd_tp env v),q,idx) ctx) exp zc ext cont
        | A.Tensor((a,p,id),b) ->
          check_exp' trace env (add_chan env (y,(a,A.perm_mult p q,id)) (update_tp env x (b,q,idx) ctx)) cont_p zc ext cont
        | _ ->
          error (exp.A.st_data) ("invalid type of " ^ x ^
                                 ", expected tensor, found: " ^ PP.pp_proto env d)
    end
  | A.Close(x) ->
    begin
      let {A.idnames = idnames ; A.permnames = permnames ; A.owned = owned ; A.locked = ldelta ; A.linear = delta} = ctx in
      if List.length delta > 0 then
        error (exp.A.st_data) ("context " ^ PP.pp_chantp_list delta ^ " not empty")
      else if List.length ldelta > 0 then
        error (exp.A.st_data) ("locked context " ^ PP.pp_chantp_list ldelta ^ " not empty")
      else if List.length owned > 0 then
        error (exp.A.st_data) ("close with owned ids " ^ PP.pp_channames owned)
      else
        match cont with
        | Some _ -> error (exp.A.st_data) ("close inside immutable operation")
        | None ->
          let (z,c) = zc in
          if x <> z then
            E.error_unknown_var (x) (exp.A.st_data)
          else
            (* "subtype is sufficient with subsync types" *)
          if not (eqtp env c A.One)
          then error (exp.A.st_data) ("type mismatch: type of " ^ x ^ ", expected: 1, " ^
                                      "found: " ^ PP.pp_proto env c)
          else ()
    end
  | A.Wait(x,cont_p) ->
    begin
      if not (has_chan x ctx)
      then E.error_unknown_var (x) (exp.A.st_data)
      else
        let (a,p,id) = find_tp x ctx (exp.A.st_data) in
        (* "subtype is sufficient with subsync types" *)
        if not (eqtp env a A.One)
        then error (exp.A.st_data) ("type mismatch: type of " ^ x ^ ", expected: 1, " ^
                                    " found: " ^ PP.pp_proto env a)
        else check_exp' trace env (remove_chan x ctx) cont_p zc ext cont
    end
  | A.Immut(ys,cont_p) ->
    begin
      let {A.idnames = idnames ; A.permnames = permnames ; A.owned = owned ; A.locked = ldelta ; A.linear = delta} = ctx in
      match cont with
      | Some _ -> error (exp.A.st_data) ("immut block inside immutable operation")
      | None ->
        if List.length ldelta > 0 then
          error (exp.A.st_data) ("locked context " ^ PP.pp_chantp_list ldelta ^ " not empty")
        else if (List.sort String.compare (List.map fst delta)) <> (List.sort String.compare ys) then
          error (exp.A.st_data) ("must name all channels (" ^ PP.pp_channames (List.map fst delta) ^ ") when entering immut block")
        else
          let delta', ldelta = List.partition (fun (x,(a,p,id)) ->
              match a with
              | A.Up _ -> p <> A.Owned && List.mem id owned
              | _ -> false) delta
          in
          let ctx' = { A.idnames = idnames ; A.permnames = permnames ; A.owned = [] ; A.locked = ldelta ; A.linear = delta' } in
          let (z,c) = zc in
          (* reorder the continuation delta to match the order of ys *)
          let delta_c = List.map (fun y -> (y,find_tp y ctx ext)) ys in
          let cont' = Some (delta_c, c, owned) in
          match c with
          | A.TpName(v) -> check_exp' trace env ctx exp (z,A.expd_tp env v) ext cont
          | A.Up(a) -> check_exp' trace env ctx' cont_p (z,a) ext cont'
          | _ ->
            error (exp.A.st_data) ("invalid type of " ^ z ^
                                 ", expected up arrow, found: " ^ PP.pp_proto env c)

    end
  | A.Continue(ys) ->
    begin
      let {A.idnames = idnames ; A.permnames = permnames ; A.owned = owned ; A.locked = ldelta ; A.linear = delta} = ctx in
      match cont with
      | None -> error (exp.A.st_data) ("continue outside of immutable operation")
      | Some (delta_c, a_c, owned_c) ->
        if List.length owned > 0 then
          error (exp.A.st_data) ("continue with owned ids " ^ PP.pp_channames owned)
        else
          let ctx' = { ctx with A.locked = [] ; A.linear = ldelta @ delta } in
          (* TODO: this does the right thing but gives kinda weird error messages *)
          let ctx' = match_ctx env delta_c ctx' ys (List.length delta_c) (List.length delta) (exp.A.st_data) in
          let delta' = ctx'.A.linear in
          if List.length delta' > 0 then
            error (exp.A.st_data) ("extra channels when continuing: " ^ PP.pp_channames (List.map fst delta'))
          else
            let (z,c) = zc in
            match c with
            | A.TpName(v) -> check_exp' trace env ctx exp (z,A.expd_tp env v) ext cont
            | A.Down(a) ->
              if not (eqtp env a a_c) then
                error (exp.A.st_data) ("type mismatch: type of " ^ z ^
                                       ", expected: " ^ PP.pp_proto env a_c ^
                                       ", found: " ^ PP.pp_proto env c)
              else
                ()
            | _ ->
              error (exp.A.st_data) ("invalid type of " ^ z ^
                                     ", expected down arrow, found: " ^ PP.pp_proto env c)

    end
  | A.Mut(cont_p) ->
    begin
      let {A.idnames = idnames ; A.permnames = permnames ; A.owned = owned ; A.locked = ldelta ; A.linear = delta} = ctx in
      match cont with
      | None -> error (exp.A.st_data) ("mut block outside of immutable operation")
      | Some (delta_c, a_c, owned_c) ->
        let ctx' = { A.idnames = idnames ; A.permnames = permnames ; A.owned = owned @ owned_c ; A.locked = [] ; A.linear = delta @ ldelta } in
        let (z,c) = zc in
          match c with
          | A.TpName(v) -> check_exp' trace env ctx exp (z,A.expd_tp env v) ext cont
          | A.DoubleDown(a) -> check_exp' trace env ctx' cont_p (z,a) ext None
          | _ ->
            error (exp.A.st_data) ("invalid type of " ^ z ^
                                 ", expected double down arrow, found: " ^ PP.pp_proto env c)
    end
  | A.Start(x,cont_p) ->
    begin
      if not (has_chan x ctx) then
        E.error_unknown_var_ctx x (exp.A.st_data)
      else (* the type a of x must be /\ *)
        let (a,p,id) = find_tp x ctx (exp.A.st_data) in
        match a with
        | A.TpName(v) -> check_exp' trace env (update_tp env x ((A.expd_tp env v),p,id) ctx) exp zc ext cont
        | A.Up(a) -> check_exp' trace env (update_tp env x (a,p,id) ctx) cont_p zc ext cont
        | _ ->
          error (exp.A.st_data) ("invalid type of " ^ x ^
                                 ", expected up arrow, found: " ^ PP.pp_proto env a)
    end
  | A.Finish(x,cont_p) ->
    begin
      if not (has_chan x ctx) then
        E.error_unknown_var_ctx x (exp.A.st_data)
      else (* the type a of x must be \/ *)
        let (a,p,id) = find_tp x ctx (exp.A.st_data) in
        match a with
        | A.TpName(v) -> check_exp' trace env (update_tp env x ((A.expd_tp env v),p,id) ctx) exp zc ext cont
        | A.Down(a) -> check_exp' trace env (update_tp env x (a,p,id) ctx) cont_p zc ext cont
        | _ ->
          error (exp.A.st_data) ("invalid type of " ^ x ^
                                 ", expected down arrow, found: " ^ PP.pp_proto env a)
    end
  | A.Mutate(x,cont_p) ->
    begin
      if not (has_chan x ctx) then
        E.error_unknown_var_ctx x (exp.A.st_data)
      else (* the type a of x must be \\// *)
        let (a,p,id) = find_tp x ctx (exp.A.st_data) in
        match p with
        | A.Fractional _ -> error (exp.A.st_data) ("mutate un-owned channel " ^ x)
        | A.Owned ->
          match a with
          | A.TpName(v) -> check_exp' trace env (update_tp env x ((A.expd_tp env v),p,id) ctx) exp zc ext cont
          | A.DoubleDown(a) -> check_exp' trace env (update_tp env x (a,p,id) ctx) cont_p zc ext cont
          | _ ->
            error (exp.A.st_data) ("invalid type of " ^ x ^
                                   ", expected double down arrow, found: " ^ PP.pp_proto env a)
    end
  | A.Split(x1,x2,x,cont_p) ->
    begin
      let (z,c) = zc in
      if has_chan x1 ctx || x1 = z then
        error (exp.A.st_data) ("variable " ^ x1 ^ " is not fresh")
      else if has_chan x2 ctx || x2 = z then
        error (exp.A.st_data) ("variable " ^ x2 ^ " is not fresh")
      else if not (has_chan x ctx) then
        E.error_unknown_var_ctx x (exp.A.st_data)
      else (* the type a of x must be /\ *)
        let (a,p,id) = find_tp x ctx (exp.A.st_data) in
        match p with
        | A.Owned -> error (exp.A.st_data) ("split owned channel " ^ x)
        | A.Fractional _ ->
          let p' = A.perm_mult p (A.perm_const 0.5) in
          let ctx' = remove_chan x ctx in
          let ctx' = add_chan env (x1, (a,p',id)) ctx' in
          let ctx' = add_chan env (x2, (a,p',id)) ctx' in
          match a with
          | A.TpName(v) -> check_exp' trace env (update_tp env x ((A.expd_tp env v),p,id) ctx) exp zc ext cont
          | A.Up(_) -> check_exp' trace env ctx' cont_p zc ext cont
          | _ ->
            error (exp.A.st_data) ("invalid type of " ^ x ^
                                   ", expected up arrow, found: " ^ PP.pp_proto env a)
    end
  | A.Merge(x,x1,x2,cont_p) ->
    begin
      let (z,c) = zc in
      if has_chan x ctx || x = z then
        error (exp.A.st_data) ("variable " ^ x ^ " is not fresh")
      else if not (has_chan x1 ctx) then
        E.error_unknown_var_ctx x1 (exp.A.st_data)
      else if not (has_chan x2 ctx) then
        E.error_unknown_var_ctx x2 (exp.A.st_data)
      else (* the type a of x1 and x2 must be /\ *)
        let (a1,p1,id1) = find_tp x1 ctx (exp.A.st_data) in
        let (a2,p2,id2) = find_tp x2 ctx (exp.A.st_data) in
        if not (A.perm_eq p1 p2) then
            error ext ("permission mismatch: permission " ^ PP.pp_perm p1 ^
                    " of " ^ x1 ^ " does not match permission " ^ PP.pp_perm p2 ^ " of " ^ x2)
        else if not (id1 = id2) then
            error ext ("id mismatch: id " ^ id1 ^ " of " ^ x1 ^ " does not match id " ^ id2 ^ " of " ^ x2)
        else if not (eqtp env a1 a2) then
            error ext ("type mismatch: type of " ^ x1 ^ " : " ^ PP.pp_proto env a1 ^
                    " does not match type of " ^ x2 ^ " : " ^ PP.pp_proto env a2)
        else
        match p1 with
        | A.Owned -> error (exp.A.st_data) ("merge owned channels " ^ x1 ^ ", " ^ x2 ^ " (something is seriously wrong)")
        | A.Fractional _ ->
          let p' = A.perm_add p1 p2 in
          let ctx' = remove_chan x1 ctx in
          let ctx' = remove_chan x2 ctx' in
          let ctx' = add_chan env (x, (a1,p',id1)) ctx' in
          match a1 with
          | A.TpName(v) -> check_exp' trace env (update_tp env x1 ((A.expd_tp env v),p1,id1) ctx) exp zc ext cont
          | A.Up(_) -> check_exp' trace env ctx' cont_p zc ext cont
          | _ ->
            error (exp.A.st_data) ("invalid type of " ^ x ^
                                   ", expected up arrow, found: " ^ PP.pp_proto env a1)
    end
  | A.Share(x,cont_p) ->
    begin
      if not (has_chan x ctx) then
        E.error_unknown_var_ctx x (exp.A.st_data)
      else (* the type a of x must be /\ *)
        let (a,p,id) = find_tp x ctx (exp.A.st_data) in
        match p with
        | A.Fractional _ -> error (exp.A.st_data) ("share un-owned channel " ^ x)
        | A.Owned ->
          let ctx' = { ctx with A.owned = id::ctx.A.owned } in
          match a with
          | A.TpName(v) -> check_exp' trace env (update_tp env x ((A.expd_tp env v),p,id) ctx) exp zc ext cont
          | A.Up(_) -> check_exp' trace env (update_tp env x (a,A.perm_const 1.,id) ctx') cont_p zc ext cont
          | _ ->
            error (exp.A.st_data) ("invalid type of " ^ x ^
                                   ", expected up arrow, found: " ^ PP.pp_proto env a)
    end
  | A.Own(x,cont_p) ->
    begin
      if not (has_chan x ctx) then
        E.error_unknown_var_ctx x (exp.A.st_data)
      else (* the type a of x must be /\ *)
        let (a,p,id) = find_tp x ctx (exp.A.st_data) in
        match p with
        | A.Owned -> error (exp.A.st_data) ("own already owned channel " ^ x)
        | A.Fractional _ ->
          if not (A.perm_eq p (A.perm_const 1.)) then
            error (exp.A.st_data) ("own channel " ^ x ^ " at non-1 permission " ^ PP.pp_perm p)
          else if not (List.mem id ctx.A.owned) then
            error (exp.A.st_data) ("own non-ownable channel " ^ x)
          else
          let ctx' = { ctx with A.owned = List.filter (fun id' -> id' <> id) ctx.A.owned } in
          match a with
          | A.TpName(v) -> check_exp' trace env (update_tp env x ((A.expd_tp env v),p,id) ctx) exp zc ext cont
          | A.Up(_) -> check_exp' trace env (update_tp env x (a,A.Owned,id) ctx') cont_p zc ext cont
          | _ ->
            error (exp.A.st_data) ("invalid type of " ^ x ^
                                   ", expected up arrow, found: " ^ PP.pp_proto env a)
    end
  | A.SendId(x,b,cont_p) ->
    begin
      if not (List.mem b ctx.A.idnames) then
        error (exp.A.st_data) ("unknown id: " ^ b)
      else
      if not (has_chan x ctx) then
        let (z,c) = zc in
        if x <> z then
          E.error_unknown_var x (exp.A.st_data)
        else (* the type c of z must be exists(id) *)
          match c with
          | A.TpName(v) -> check_exp' trace env ctx exp (z,A.expd_tp env v) ext cont
          | A.ExistsId(k,a) -> check_exp' trace env ctx cont_p (z,A.proto_subst_id b k a) ext cont
          | _ ->
            error (exp.A.st_data) ("invalid type of " ^ x ^
                                   ", expected exists(id), found: " ^ PP.pp_proto env c)
      else (* the type a of x must be forall(id) *)
        let (a,p,id) = find_tp x ctx (exp.A.st_data) in
        match a with
        | A.TpName(v) -> check_exp' trace env (update_tp env x ((A.expd_tp env v),p,id) ctx) exp zc ext cont
        | A.ForallId(k,a) -> check_exp' trace env (update_tp env x (A.stype_subst_id b k (a,p,id)) ctx) cont_p zc ext cont
        | _ ->
          error (exp.A.st_data) ("invalid type of " ^ x ^
                                 ", expected forall(id), found: " ^ PP.pp_proto env a)

    end
  | A.RecvId(x,b,cont_p) ->
    begin
      if List.mem b ctx.A.idnames then
        error (exp.A.st_data) ("id " ^ b ^ " is not fresh")
      else
      if not (has_chan x ctx) then
        let (z,c) = zc in
        if x <> z then
          E.error_unknown_var x (exp.A.st_data)
        else (* the type c of z must be forall(id) *)
          let ctx' = { ctx with A.idnames = b::ctx.A.idnames } in
          match c with
          | A.TpName(v) -> check_exp' trace env ctx exp (z,A.expd_tp env v) ext cont
          | A.ForallId(k,a) -> check_exp' trace env ctx' cont_p (z,A.proto_subst_id b k a) ext cont
          | _ ->
            error (exp.A.st_data) ("invalid type of " ^ x ^
                                   ", expected forall(id), found: " ^ PP.pp_proto env c)
      else (* the type a of x must be exists(id) *)
        let (a,p,id) = find_tp x ctx (exp.A.st_data) in
        let ctx' = { ctx with A.idnames = b::ctx.A.idnames } in
        match a with
        | A.TpName(v) -> check_exp' trace env (update_tp env x ((A.expd_tp env v),p,id) ctx) exp zc ext cont
        | A.ExistsId(k,a) -> check_exp' trace env (update_tp env x (A.stype_subst_id b k (a,p,id)) ctx') cont_p zc ext cont
        | _ ->
          error (exp.A.st_data) ("invalid type of " ^ x ^
                                 ", expected exists(id), found: " ^ PP.pp_proto env a)
    end
  | A.SendPerm(x,p,cont_p) ->
    begin
      if not (check_perm p ctx) then
        error (exp.A.st_data) ("invalid permission: " ^ PP.pp_perm p)
      else
      if not (has_chan x ctx) then
        let (z,c) = zc in
        if x <> z then
          E.error_unknown_var x (exp.A.st_data)
        else (* the type c of z must be exists(perm) *)
          match c with
          | A.TpName(v) -> check_exp' trace env ctx exp (z,A.expd_tp env v) ext cont
          | A.ExistsPerm(k,a) -> check_exp' trace env ctx cont_p (z,A.proto_subst_perm p k a) ext cont
          | _ ->
            error (exp.A.st_data) ("invalid type of " ^ x ^
                                   ", expected exists(perm), found: " ^ PP.pp_proto env c)
      else (* the type a of x must be forall(perm) *)
        let (a,p,id) = find_tp x ctx (exp.A.st_data) in
        match a with
        | A.TpName(v) -> check_exp' trace env (update_tp env x ((A.expd_tp env v),p,id) ctx) exp zc ext cont
        | A.ForallPerm(k,a) -> check_exp' trace env (update_tp env x (A.stype_subst_perm p k (a,p,id)) ctx) cont_p zc ext cont
        | _ ->
          error (exp.A.st_data) ("invalid type of " ^ x ^
                                 ", expected forall(perm), found: " ^ PP.pp_proto env a)

    end
  | A.RecvPerm(x,p,cont_p) ->
    begin
      if List.mem p ctx.A.idnames then
        error (exp.A.st_data) ("permission name " ^ p ^ " is not fresh")
      else
      if not (has_chan x ctx) then
        let (z,c) = zc in
        if x <> z then
          E.error_unknown_var x (exp.A.st_data)
        else (* the type c of z must be forall(perm) *)
          let ctx' = { ctx with A.permnames = p::ctx.A.permnames } in
          match c with
          | A.TpName(v) -> check_exp' trace env ctx exp (z,A.expd_tp env v) ext cont
          | A.ForallPerm(k,a) -> check_exp' trace env ctx' cont_p (z,A.proto_subst_perm (A.perm_var p) k a) ext cont
          | _ ->
            error (exp.A.st_data) ("invalid type of " ^ x ^
                                   ", expected forall(perm), found: " ^ PP.pp_proto env c)
      else (* the type a of x must be exists(perm) *)
        let (a,p',id) = find_tp x ctx (exp.A.st_data) in
        let ctx' = { ctx with A.permnames = p::ctx.A.permnames } in
        match a with
        | A.TpName(v) -> check_exp' trace env (update_tp env x ((A.expd_tp env v),p',id) ctx) exp zc ext cont
        | A.ExistsPerm(k,a) -> check_exp' trace env (update_tp env x (A.stype_subst_perm (A.perm_var p) k (a,p',id)) ctx') cont_p zc ext cont
        | _ ->
          error (exp.A.st_data) ("invalid type of " ^ x ^
                                 ", expected exists(perm), found: " ^ PP.pp_proto env a)
    end
  | A.Abort -> ()
  | A.Print(l,args,p) ->
    begin
      let () = check_printable_list ctx (exp.A.st_data) l args (List.length (filter_args l)) (List.length args) in
      check_exp' trace env ctx p zc ext cont
    end

and check_branchesR trace env ctx branches z choices ext cont = match branches, choices with
    (l1,p)::branches', (l2,c)::choices' ->
    begin
        if trace then print_string ("| " ^ l1 ^ " => \n") else ()
        ; if l1 = l2 then () else E.error_label_mismatch (l1, l2) ext
        ; check_exp' trace env ctx p (z,c) (p.A.st_data) cont
        ; check_branchesR trace env ctx branches' z choices' ext cont
    end
    | [], [] -> ()
    | (l,_p)::_branches', [] ->
        E.error_label_missing_alt (l) ext
    | [], (l,_c)::_choices' ->
        E.error_label_missing_branch (l) ext

and check_branchesL trace env ctx x choices branches zc ext cont = match choices, branches with
    (l1,a)::choices', (l2,cont_p)::branches' ->
    begin
        if trace then print_string ("| " ^ l1 ^ " => \n") else ()
        ; if l1 = l2 then () else E.error_label_mismatch (l1, l2) ext
        ; let (_,p,id) = find_tp x ctx ext in
          check_exp' trace env (update_tp env x (a,p,id) ctx) cont_p zc (cont_p.A.st_data) cont
        ; check_branchesL trace env ctx x choices' branches' zc ext cont
    end
    | [], [] -> ()
    | [], (l,_p)::_branches' ->
        E.error_label_missing_alt (l) ext
    | (l,_a)::_choices', [] ->
        E.error_label_missing_branch (l) ext

      (* let rec link_tps env state_channels args odelta ext =
           match args, odelta with
               [], [] -> ()
             | (A.FArg e)::_args', (A.Functional _)::_odelta' ->
                 linkerror ext ("functional arguments not allowed in executing process: " ^ PP.pp_fexp env 0 e)
             | (A.FArg e)::_args', (A.STyped _)::_odelta' ->
                 linkerror ext ("expected session-typed argument, found functional argument: " ^ PP.pp_fexp env 0 e)
             | (A.STArg c)::_args', (A.Functional _)::_odelta' ->
                 linkerror ext ("expected functional argument, found channel: " ^ c)
             | [], _hd::_tl -> raise UnknownTypeError
             | _hd::_tl, [] -> raise UnknownTypeError
             | (A.STArg c)::args', (A.STyped(_x,sigt))::odelta' ->
                 match M.find state_channels c with
                     None -> raise UnknownTypeError
                   | Some t ->
                       if not (subtp env t sigt)
                       then linkerror ext ("type mismatch of " ^ c ^
                                           " expected: " ^ PP.pp_proto env sigt ^
                                           ", found: " ^ PP.pp_proto env t)
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
           then error ext ("asset process " ^ f ^ " has offered channel at mode " ^ x)
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
           then error ext ("shared process " ^ f ^ " has offered channel at mode " ^ x)
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
           then error ext ("transaction process " ^ f ^ " has offered channel at mode " ^ x)
           else if not (mode_S_list sdelta)
           then error ext ("transaction process " ^ f ^ " has shared context not at shared mode: " ^ PP.pp_lsctx env sdelta)
           else if not (mode_lin_list ldelta)
           then error ext ("transaction process " ^ f ^ " has linear context not at linear mode: " ^ PP.pp_lsctx env ldelta)
           else ();; *)
