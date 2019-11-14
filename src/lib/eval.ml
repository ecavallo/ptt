module Syn = Syntax
module D = Domain

exception Eval_failed of string

let eval_dim r (env : D.env) =
  match r with
  | Syn.DVar i ->
    begin
      match List.nth env i with
      | D.Dim s -> s
      | D.Tm _ -> raise (Eval_failed "Not a dimension term")
    end
  | Syn.Const o -> D.Const o

let rec do_clos size clo a =
  match clo with
  | D.Clos {term; env} -> eval term (a :: env) size
  | D.Pseudo {var; term; ends} ->
    begin
      match a with
      | D.Dim (D.DVar i) -> D.instantiate i var term
      | D.Dim (D.Const o) -> List.nth ends o
      | D.Tm _ -> raise (Eval_failed "Applied psuedo-closure to term")
    end

and do_clos2 size (D.Clos2 {term; env}) a1 a2 =
  eval term (a2 :: a1 :: env) size

and do_clos3 size (D.Clos3 {term; env}) t1 t2 t3 =
  eval term (D.Tm t3 :: D.Tm t2 :: D.Tm t1 :: env) size

and do_closN size (D.ClosN {term; env}) tN =
  eval term (List.rev_append (List.map (fun t -> D.Tm t) tN) env) size

and do_clos_extent size (D.ClosN {term; env}) tN t r =
  eval term (D.Dim r :: D.Tm t :: List.rev_append (List.map (fun t -> D.Tm t) tN) env) size

and do_consts size clo width =
  match clo with
  | D.Clos {term; env} ->
    List.init width (fun o -> eval term (D.Dim (D.Const o) :: env) size)
  | D.Pseudo {ends; _} -> ends

and do_rec size tp zero suc n =
  match n with
  | D.Zero -> zero
  | D.Suc n -> do_clos2 size suc (D.Tm n) (D.Tm (do_rec size tp zero suc n))
  | D.Neutral {term; _} ->
    let final_tp = do_clos size tp (D.Tm n) in
    D.Neutral {tp = final_tp; term = D.(NRec (tp, zero, suc) @: term)}
  | _ -> raise (Eval_failed "Not a number")

and do_if size mot tt ff b =
  match b with
  | D.True -> tt
  | D.False -> ff
  | D.Neutral {term; _} ->
    let final_tp = do_clos size mot (D.Tm b) in
    D.Neutral {tp = final_tp; term = D.(If (mot, tt, ff) @: term)}
  | _ -> raise (Eval_failed "Not a number")

and do_fst p =
  match p with
  | D.Pair (p1, _) -> p1
  | D.Neutral {tp; term} ->
    D.Neutral {tp = do_sg_dom tp; term = D.(Fst @: term)}
  | _ -> raise (Eval_failed "Couldn't fst argument in do_fst")

and do_snd size p =
  match p with
  | D.Pair (_, p2) -> p2
  | D.Neutral {tp; term} ->
    let fst = do_fst p in
    D.Neutral {tp = do_pi_cod size tp fst; term = D.(Snd @: term)}
  | _ -> raise (Eval_failed "Couldn't snd argument in do_snd")

and do_bapp size t r =
  match t with
  | D.BLam bclo -> do_clos size bclo (D.Dim r)
  | D.Neutral {tp; term} ->
    begin 
      match r with 
      | D.DVar i -> 
        let dst = do_bridge_cod size tp r in 
        D.Neutral {tp = dst; term = D.(BApp i @: term)}
      | Const o -> 
        do_bridge_endpoint tp r o
    end
  | _ -> raise (Eval_failed "Not a bridge or neutral in bapp")

and do_j size mot refl eq =
  match eq with
  | D.Refl t -> do_clos size refl (D.Tm t)
  | D.Neutral {tp; term = term} ->
    let tp = do_id_tp tp in
    let left = do_id_left tp in
    let right = do_id_right tp in
    D.Neutral
      {tp = do_clos3 size mot left right eq;
       term = D.(J (mot, refl, tp, left, right) @: term)}
  | _ -> raise (Eval_failed "Not a refl or neutral in do_j")

and do_ap size f a =
  match f with
  | D.Lam clos -> do_clos size clos (D.Tm a)
  | D.Neutral {tp; term} ->
    let src = do_pi_dom tp in
    let dst = do_pi_cod size tp a in
    D.Neutral {tp = dst; term = D.(Ap (D.Normal {tp = src; term = a}) @: term)}
  | _ -> raise (Eval_failed "Not a function in do_ap")


and do_id_tp tp = 
  match tp with 
  | D.Id (tp, _, _) -> tp
  | D.Neutral {tp; term} ->
    D.Neutral {tp; term = D.(Quasi IdTp @: term)}
  | _ -> raise (Eval_failed "Not something that can become a identity type")


and do_id_left tp = 
  match tp with 
  | D.Id (_, l, _) -> l
  | D.Neutral {tp; term} ->
    D.Neutral {tp = D.(Neutral {tp; term = Quasi IdTp @: term}); term = D.(Quasi IdLeft @: term)}
  | _ -> raise (Eval_failed "Not something that can become a identity type")


and do_id_right tp = 
  match tp with 
  | D.Id (_, _, r) -> r
  | D.Neutral {tp; term} ->
    D.Neutral {tp = D.(Neutral {tp; term = Quasi IdTp @: term}); term = D.(Quasi IdRight @: term)}
  | _ -> raise (Eval_failed "Not something that can become a identity type")


and do_bridge_cod size tp s =
  match tp with
  | D.Bridge (clos, _) ->
    do_clos size clos (D.Dim s)
  | D.Neutral {tp; term} ->
    D.Neutral {tp; term = D.(Quasi (BridgeCod s) @: term)}
  | _ -> raise (Eval_failed "Not something that can be come a bridge type")

and do_bridge_endpoint tp s o =
  match tp with
  | D.Bridge (_, ts) ->
    List.nth ts o
  | D.Neutral {tp; term} ->
    D.Neutral {tp = D.Neutral {tp; term = D.(Quasi (BridgeCod s) @: term)}; term = D.(Quasi (BridgeEndpoint (s,o)) @: term)}
  | _ -> raise (Eval_failed "Not something that can be come a bridge type")

and do_pi_dom f = 
  match f with 
  | D.Pi (tp, _) -> tp
  | D.Neutral {tp; term} ->
    D.Neutral {tp; term = D.(Quasi PiDom @: term)}
  | _ -> raise (Eval_failed "Not something that can become a pi type")

and do_pi_cod size f a = 
  match f with 
  | D.Pi (_,dst) -> do_clos size dst (D.Tm a)
  | D.Neutral {tp; term} ->
    D.Neutral {tp; term = D.(Quasi (PiCod a) @: term)}
  | _ -> raise (Eval_failed "Not something that can become a pi type")


and do_sg_dom f = 
  match f with 
  | D.Sg (tp, _) -> tp
  | D.Neutral {tp; term} ->
    D.Neutral {tp; term = D.(Quasi SgDom @: term)}
  | _ -> raise (Eval_failed "Not something that can become a sigma type")

and do_sg_cod size f a = 
  match f with 
  | D.Sg (_,dst) -> do_clos size dst (D.Tm a)
  | D.Neutral {tp; term} ->
    D.Neutral {tp; term = D.(Quasi (SgCod a) @: term)}
  | _ -> raise (Eval_failed "Not something that can become a sigma type")


and do_ungel size ends mot gel case =
  begin
    match gel with
    | D.Engel (_, _, t) -> do_clos size case (D.Tm t)
    | D.Neutral {tp; term} ->
      begin
        match tp with
        | D.Gel (_, end_tps, rel) ->
          let end_nos = List.map2 (fun tp term -> (D.Normal {tp; term})) end_tps ends in
          let final_tp =
            do_clos size mot (D.Tm (D.BLam (D.Pseudo {var = size; term = gel; ends}))) in
          D.Neutral {tp = final_tp; term = D.(Ungel (end_nos, rel, mot, size, case) @: term)}
        | _ -> raise (Eval_failed "Not a Gel in do_ungel")
      end
    | _ -> raise (Eval_failed "Not a gel or neutral in do_ungel")
  end

and eval t (env : D.env) size =
  match t with
  | Syn.Var i ->
    begin
      match List.nth env i with
      | D.Tm t -> t
      | D.Dim _-> raise (Eval_failed "Not a term variable")
    end
  | Syn.Let (def, body) -> eval body (D.Tm (eval def env size) :: env) size
  | Syn.Check (term, _) -> eval term env size
  | Syn.Unit -> D.Unit
  | Syn.Triv -> D.Triv
  | Syn.Nat -> D.Nat
  | Syn.Zero -> D.Zero
  | Syn.Suc t -> D.Suc (eval t env size)
  | Syn.NRec (tp, zero, suc, n) ->
    do_rec size
      (Clos {term = tp; env})
      (eval zero env size)
      (Clos2 {term = suc; env})
      (eval n env size)
  | Syn.Bool -> D.Bool
  | Syn.True -> D.True
  | Syn.False -> D.False
  | Syn.If (mot, tt, ff, b) ->
    do_if size
      (Clos {term = mot; env})
      (eval tt env size)
      (eval ff env size)
      (eval b env size)
  | Syn.Pi (src, dest) ->
    D.Pi (eval src env size, (Clos {term = dest; env}))
  | Syn.Lam t -> D.Lam (Clos {term = t; env})
  | Syn.Ap (t1, t2) -> do_ap size (eval t1 env size) (eval t2 env size)
  | Syn.Uni i -> D.Uni i
  | Syn.Sg (t1, t2) -> D.Sg (eval t1 env size, (Clos {term = t2; env}))
  | Syn.Pair (t1, t2) -> D.Pair (eval t1 env size, eval t2 env size)
  | Syn.Fst t -> do_fst (eval t env size)
  | Syn.Snd t -> do_snd size (eval t env size)
  | Syn.Bridge (dest, ts) -> D.Bridge (Clos {term = dest; env}, List.map (fun t -> eval t env size) ts)
  | Syn.BApp (t,r) ->
    let r' = eval_dim r env in
    do_bapp size (eval t env size) r'
  | Syn.BLam t -> D.BLam (Clos {term = t; env})
  | Syn.Refl t -> D.Refl (eval t env size)
  | Syn.Id (tp, left, right) -> D.Id (eval tp env size, eval left env size, eval right env size)
  | Syn.J (mot, refl, eq) ->
    do_j size (D.Clos3 {term = mot; env}) (D.Clos {term = refl; env}) (eval eq env size)
  | Syn.Extent (r, dom, mot, ctx, endcase, varcase) ->
    let r' = eval_dim r env in
    let ctx' = eval ctx env size in
    begin
      match r' with
      | D.DVar i ->
        let final_tp = eval mot (D.Tm ctx' :: D.Dim r' :: env) size in
        let ext =
          D.Ext
            {var = i;
             dom = D.Clos {term = dom; env};
             mot = D.Clos2 {term = mot; env};
             ctx = ctx';
             endcase = List.map (fun t -> D.Clos {term = t; env}) endcase;
             varcase = D.ClosN {term = varcase; env}}
        in
        D.Neutral {tp = final_tp; term = D.root ext}
      | D.Const o ->
        eval (List.nth endcase o) (D.Tm ctx' :: env) size
    end
  | Syn.Gel (r, endtps, rel) ->
    begin
      let r' = eval_dim r env in
      match r' with
      | D.DVar i -> D.Gel (i, List.map (fun t -> eval t env size) endtps, D.ClosN {term = rel; env})
      | D.Const o -> eval (List.nth endtps o) env size
    end
  | Syn.Engel (i, ts, t) ->
    begin
      let r' = eval_dim (Syn.DVar i) env in
      match r' with
      | D.DVar i' -> D.Engel (i', List.map (fun t -> eval t env size) ts, eval t env size)
      | Const o -> eval (List.nth ts o) env size
    end
  | Syn.Ungel (width, mot, gel, case) ->
    do_ungel
      size
      (do_consts size (D.Clos {term = gel; env}) width)
      (D.Clos {term = mot; env})
      (eval gel (D.Dim (D.DVar size) :: env) (size + 1))
      (D.Clos {term = case; env})
