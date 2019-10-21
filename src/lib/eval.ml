module Syn = Syntax
module D = Domain

exception Eval_failed of string

let eval_bdim r (env : D.env) =
  match r with
  | Syn.BVar i ->
    begin
      match List.nth env i with
      | D.BDim s -> s
      | D.Term _ -> raise (Eval_failed "Not a dimension term")
    end

(* TODO organize these closure functions in a better way *)

let rec do_bclos size clo r =
  match clo with
  | D.Clos {term; env} -> eval term (D.BDim r :: env) size
  | D.ConstClos t -> t

and do_clos size clo a =
  match clo with
  | D.Clos {term; env} -> eval term (D.Term a :: env) size
  | D.ConstClos t -> t

and do_clos2 size (D.Clos2 {term; env}) a1 a2 =
  eval term (D.Term a2 :: D.Term a1 :: env) size

and do_bclosclos size (D.Clos2 {term; env}) r a =
  eval term (D.Term a :: D.BDim r :: env) size

and do_closbclos size (D.Clos2 {term; env}) a r =
  eval term (D.BDim r :: D.Term a :: env) size

and do_clos3 size (D.Clos3 {term; env}) a1 a2 a3 =
  eval term (D.Term a3 :: D.Term a2 :: D.Term a1 :: env) size

and do_rec size tp zero suc n =
  match n with
  | D.Zero -> zero
  | D.Suc n -> do_clos2 size suc n (do_rec size tp zero suc n)
  | D.Neutral {term; _} ->
    let final_tp = do_clos size tp n in
    D.Neutral {tp = final_tp; term = D.NRec (tp, zero, suc, term)}
  | D.Extent {term; _} ->
    let final_tp = do_clos size tp n in
    D.Extent {tp = final_tp; term = D.NRec (tp, zero, suc, term)}
  | _ -> raise (Eval_failed "Not a number")

and do_fst p =
  match p with
  | D.Pair (p1, _) -> p1
  | D.Neutral {tp = D.Sg (t, _); term} ->
    D.Neutral {tp = t; term = D.Fst term}
  | D.Extent {tp = D.Sg (t, _); term} ->
    D.Extent {tp = t; term = D.Fst term}
  | _ -> raise (Eval_failed "Couldn't fst argument in do_fst")

and do_snd size p =
  match p with
  | D.Pair (_, p2) -> p2
  | D.Neutral {tp = D.Sg (_, clo); term} ->
    let fst = do_fst p in
    D.Neutral {tp = do_clos size clo fst; term = D.Snd term}
  | D.Extent {tp = D.Sg (_, clo); term} ->
    let fst = do_fst p in
    D.Extent {tp = do_clos size clo fst; term = D.Snd term}
  | _ -> raise (Eval_failed "Couldn't snd argument in do_snd")

and do_bapp size t r =
  match t with
  | D.BLam bclo -> do_bclos size bclo r
  | D.Neutral {tp; term} ->
    begin
      match r with
      | D.BVar i ->
        begin
          match tp with
          | D.Bridge dst ->
            let dst = do_bclos size dst r in
            D.Neutral {tp = dst; term = D.BApp (term, i)}
          | _ -> raise (Eval_failed "Not a bridge in do_bapp")
        end
    end
  | D.Extent {tp; term} ->
    begin
      match r with
      | D.BVar i ->
        begin
          match tp with
          | D.Bridge dst ->
            let dst = do_bclos size dst r in
            D.Extent {tp = dst; term = D.BApp (term, i)}
          | _ -> raise (Eval_failed "Not a bridge in do_bapp")
        end
    end
  | _ -> raise (Eval_failed "Not a bridge or neutral in bapp")

and do_j size mot refl eq =
  match eq with
  | D.Refl t -> do_clos size refl t
  | D.Neutral {tp; term = term} ->
    begin
      match tp with
      | D.Id (tp, left, right) ->
        D.Neutral
          {tp = do_clos3 size mot left right eq;
           term = D.J (mot, refl, tp, left, right, term)}
      | _ -> raise (Eval_failed "Not an Id in do_j")
    end
  | D.Extent {tp; term = term} ->
    begin
      match tp with
      | D.Id (tp, left, right) ->
        D.Extent
          {tp = do_clos3 size mot left right eq;
           term = D.J (mot, refl, tp, left, right, term)}
      | _ -> raise (Eval_failed "Not an Id in do_j")
    end
  | _ -> raise (Eval_failed "Not a refl or neutral in do_j")

and do_ap size f a =
  match f with
  | D.Lam clos -> do_clos size clos a
  | D.Neutral {tp; term} ->
    begin
      match tp with
      | D.Pi (src, dst) ->
        let dst = do_clos size dst a in
        D.Neutral {tp = dst; term = D.Ap (term, D.Normal {tp = src; term = a})}
      | _ -> raise (Eval_failed "Not a Pi in do_ap")
    end
  | D.Extent {tp; term} ->
    begin
      match tp with
      | D.Pi (src, dst) ->
        let dst = do_clos size dst a in
        D.Extent {tp = dst; term = D.Ap (term, D.Normal {tp = src; term = a})}
      | _ -> raise (Eval_failed "Not a Pi in do_ap")
    end
  | _ -> raise (Eval_failed "Not a function in do_ap")

and do_ungel size mot i gel clo case =
  begin
    match gel with
    | D.Engel (_, t) -> do_clos size case t
    | D.Neutral {tp; term} ->
      begin
        match tp with
        | D.Gel (_, tp) ->
          let final_tp = do_clos size mot (D.BLam clo) in
          D.Neutral {tp = final_tp; term = D.Ungel (tp, mot, i, term, clo, case)}
        | _ -> raise (Eval_failed "Not a Gel in do_ungel")
      end
    | D.Extent {tp; term} ->
      begin
        match tp with
        | D.Gel (_, tp) ->
          let final_tp = do_clos size mot (D.BLam clo) in
          D.Extent {tp = final_tp; term = D.Ungel (tp, mot, i, term, clo, case)}
        | _ -> raise (Eval_failed "Not a Gel in do_ungel")
      end
    | _ -> raise (Eval_failed "Not a gel or neutral in do_ungel")
  end

and eval t (env : D.env) size =
  match t with
  | Syn.Var i ->
    begin
      match List.nth env i with
      | D.Term t -> t
      | D.BDim _-> raise (Eval_failed "Not a term variable")
    end
  | Syn.Let (def, body) -> eval body (D.Term (eval def env size) :: env) size
  | Syn.Check (term, _) -> eval term env size
  | Syn.Nat -> D.Nat
  | Syn.Zero -> D.Zero
  | Syn.Suc t -> D.Suc (eval t env size)
  | Syn.NRec (tp, zero, suc, n) ->
    do_rec size
      (Clos {term = tp; env})
      (eval zero env size)
      (Clos2 {term = suc; env})
      (eval n env size)
  | Syn.Pi (src, dest) ->
    D.Pi (eval src env size, (Clos {term = dest; env}))
  | Syn.Lam t -> D.Lam (Clos {term = t; env})
  | Syn.Ap (t1, t2) -> do_ap size (eval t1 env size) (eval t2 env size)
  | Syn.Uni i -> D.Uni i
  | Syn.Sg (t1, t2) -> D.Sg (eval t1 env size, (Clos {term = t2; env}))
  | Syn.Pair (t1, t2) -> D.Pair (eval t1 env size, eval t2 env size)
  | Syn.Fst t -> do_fst (eval t env size)
  | Syn.Snd t -> do_snd size (eval t env size)
  | Syn.Bridge dest -> D.Bridge (Clos {term = dest; env})
  | Syn.BApp (t,r) ->
    let r' = eval_bdim r env in
    do_bapp size (eval t env size) r'
  | Syn.BLam t -> D.BLam (Clos {term = t; env})
  | Syn.Refl t -> D.Refl (eval t env size)
  | Syn.Id (tp, left, right) -> D.Id (eval tp env size, eval left env size, eval right env size)
  | Syn.J (mot, refl, eq) ->
    do_j size (D.Clos3 {term = mot; env}) (D.Clos {term = refl; env}) (eval eq env size)
  | Syn.Extent (r, dom, mot, ctx, varcase) ->
    let r' = eval_bdim r env in
    begin
      match r' with
      | D.BVar i ->
        let ctx' = eval ctx env size in
        let final_tp = eval mot (D.Term ctx' :: D.BDim r' :: env) size in
        let ext =
          D.Ext
            {var = i;
             dom = D.Clos {term = dom; env};
             mot = D.Clos2 {term = mot; env};
             ctx = ctx';
             varcase = D.Clos2 {term = varcase; env}}
        in
        D.Extent {tp = final_tp; term = D.Root ext}
    end
  | Syn.Gel (r, t) ->
    begin
      let r' = eval_bdim r env in
      match r' with
      | D.BVar i -> D.Gel (i, eval t env size)
    end
  | Syn.Engel (r, t) ->
    begin
      let r' = eval_bdim r env in
      match r' with
      | D.BVar i -> D.Engel (i, eval t env size)
    end
  | Syn.Ungel (mot, gel, case) ->
    do_ungel
      size
      (D.Clos {term = mot; env})
      size
      (eval gel (D.BDim (D.BVar size) :: env) (size + 1))
      (D.Clos {term = gel; env})
      (D.Clos {term = case; env})
