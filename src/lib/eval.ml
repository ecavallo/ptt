module Syn = Syntax
module D = Domain

exception Eval_failed of string

let restrict_env r (entries, range) =
  let rec go i entries =
    match i, entries with
    | 0, D.BDim _ :: entries -> entries
    | _, D.BDim s :: entries -> D.BDim s :: go (i - 1) entries
    | _, D.Term _ :: entries -> go (i - 1) entries
    | _ -> raise (Eval_failed "Failed to restrict semantic entriesironment")
  in
  match r with
  | Syn.BVar i -> (go i entries, range)

let eval_bdim r (env : D.env) =
  match r with
  | Syn.BVar i ->
    begin
      let (entries, _) = env in
      match List.nth entries i with
      | D.BDim s -> s
      | D.Term _ -> raise (Eval_failed "Not a dimension term")
    end

(* TODO organize these closure functions in a better way *)

let rec do_bclos range clo r =
  match clo with
  | D.Clos {term; env} -> eval term (D.add_bdim r (D.resize_env range env))
  | D.ConstClos t -> t

and do_clos range clo a =
  match clo with
  | D.Clos {term; env} -> eval term (D.add_term a (D.resize_env range env))
  | D.ConstClos t -> t

and do_clos2 range (D.Clos2 {term; env}) a1 a2 =
  eval term (D.add_term a2 (D.add_term a1 (D.resize_env range env)))

and do_bclosclos range (D.Clos2 {term; env}) r a =
  eval term (D.add_term a (D.add_bdim r (D.resize_env range env)))

and do_closbclos range (D.Clos2 {term; env}) a r =
  eval term (D.add_bdim r (D.add_term a (D.resize_env range env)))

and do_clos3 range (D.Clos3 {term; env}) a1 a2 a3 =
  eval term (D.add_term a3 (D.add_term a2 (D.add_term a1 (D.resize_env range env))))

and do_rec range tp zero suc n =
  match n with
  | D.Zero -> zero
  | D.Suc n -> do_clos2 range suc n (do_rec range tp zero suc n)
  | D.Neutral {term; _} ->
    let final_tp = do_clos range tp n in
    D.Neutral {tp = final_tp; term = D.NRec (tp, zero, suc, term)}
  | D.Extent {term; _} ->
    let final_tp = do_clos range tp n in
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

and do_snd range p =
  match p with
  | D.Pair (_, p2) -> p2
  | D.Neutral {tp = D.Sg (_, clo); term} ->
    let fst = do_fst p in
    D.Neutral {tp = do_clos range clo fst; term = D.Snd term}
  | D.Extent {tp = D.Sg (_, clo); term} ->
    let fst = do_fst p in
    D.Extent {tp = do_clos range clo fst; term = D.Snd term}
  | _ -> raise (Eval_failed "Couldn't snd argument in do_snd")

and do_bapp range t r =
  match t with
  | D.BLam bclo -> do_bclos range bclo r
  | D.Neutral {tp; term} ->
    begin
      match r with
      | D.BVar i ->
        begin
          match tp with
          | D.Bridge dst ->
            let dst = do_bclos range dst r in
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
            let dst = do_bclos range dst r in
            D.Extent {tp = dst; term = D.BApp (term, i)}
          | _ -> raise (Eval_failed "Not a bridge in do_bapp")
        end
    end
  | _ -> raise (Eval_failed "Not a bridge or neutral in bapp")

and do_j range mot refl eq =
  match eq with
  | D.Refl t -> do_clos range refl t
  | D.Neutral {tp; term = term} ->
    begin
      match tp with
      | D.Id (tp, left, right) ->
        D.Neutral
          {tp = do_clos3 range mot left right eq;
           term = D.J (mot, refl, tp, left, right, term)}
      | _ -> raise (Eval_failed "Not an Id in do_j")
    end
  | D.Extent {tp; term = term} ->
    begin
      match tp with
      | D.Id (tp, left, right) ->
        D.Extent
          {tp = do_clos3 range mot left right eq;
           term = D.J (mot, refl, tp, left, right, term)}
      | _ -> raise (Eval_failed "Not an Id in do_j")
    end
  | _ -> raise (Eval_failed "Not a refl or neutral in do_j")

and do_ap range f a =
  match f with
  | D.Lam clos -> do_clos range clos a
  | D.Neutral {tp; term} ->
    begin
      match tp with
      | D.Pi (src, dst) ->
        let dst = do_clos range dst a in
        D.Neutral {tp = dst; term = D.Ap (term, D.Normal {tp = src; term = a})}
      | _ -> raise (Eval_failed "Not a Pi in do_ap")
    end
  | D.Extent {tp; term} ->
    begin
      match tp with
      | D.Pi (src, dst) ->
        let dst = do_clos range dst a in
        D.Extent {tp = dst; term = D.Ap (term, D.Normal {tp = src; term = a})}
      | _ -> raise (Eval_failed "Not a Pi in do_ap")
    end
  | _ -> raise (Eval_failed "Not a function in do_ap")

and do_ungel range mot i gel clo case =
  begin
    match gel with
    | D.Engel (_, t) -> do_clos range case t
    | D.Neutral {tp; term} ->
      begin
        match tp with
        | D.Gel (_, tp) ->
          let final_tp = do_clos range mot (D.BLam clo) in
          D.Neutral {tp = final_tp; term = D.Ungel (tp, mot, i, term, clo, case)}
        | _ -> raise (Eval_failed "Not a Gel in do_ungel")
      end
    | D.Extent {tp; term} ->
      begin
        match tp with
        | D.Gel (_, tp) ->
          let final_tp = do_clos range mot (D.BLam clo) in
          D.Extent {tp = final_tp; term = D.Ungel (tp, mot, i, term, clo, case)}
        | _ -> raise (Eval_failed "Not a Gel in do_ungel")
      end
    | _ -> raise (Eval_failed "Not a gel or neutral in do_ungel")
  end

and eval t (env : D.env) =
  match t with
  | Syn.Var i ->
    begin
      let (entries, _) = env in
      match List.nth entries i with
      | D.Term t -> t
      | D.BDim _-> raise (Eval_failed "Not a term variable")
    end
  | Syn.Let (def, body) -> eval body (D.add_term (eval def env) env)
  | Syn.Check (term, _) -> eval term env
  | Syn.Nat -> D.Nat
  | Syn.Zero -> D.Zero
  | Syn.Suc t -> D.Suc (eval t env)
  | Syn.NRec (tp, zero, suc, n) ->
    do_rec
      (D.get_range env)
      (Clos {term = tp; env})
      (eval zero env)
      (Clos2 {term = suc; env})
      (eval n env)
  | Syn.Pi (src, dest) ->
    D.Pi (eval src env, (Clos {term = dest; env}))
  | Syn.Lam t -> D.Lam (Clos {term = t; env})
  | Syn.Ap (t1, t2) -> do_ap (D.get_range env) (eval t1 env) (eval t2 env)
  | Syn.Uni i -> D.Uni i
  | Syn.Sg (t1, t2) -> D.Sg (eval t1 env, (Clos {term = t2; env}))
  | Syn.Pair (t1, t2) -> D.Pair (eval t1 env, eval t2 env)
  | Syn.Fst t -> do_fst (eval t env)
  | Syn.Snd t -> do_snd (D.get_range env) (eval t env)
  | Syn.Bridge dest -> D.Bridge (Clos {term = dest; env})
  | Syn.BApp (t,r) ->
    let r' = eval_bdim r env in
    do_bapp (D.get_range env) (eval t (restrict_env r env)) r'
  | Syn.BLam t -> D.BLam (Clos {term = t; env})
  | Syn.Refl t -> D.Refl (eval t env)
  | Syn.Id (tp, left, right) -> D.Id (eval tp env, eval left env, eval right env)
  | Syn.J (mot, refl, eq) ->
    do_j (D.get_range env) (D.Clos3 {term = mot; env}) (D.Clos {term = refl; env}) (eval eq env)
  | Syn.Extent (r, dom, mot, ctx, varcase) ->
    let r' = eval_bdim r env in
    begin
      match r' with
      | D.BVar i ->
        let ctx' = eval ctx env in
        let restricted_env = restrict_env r env in
        let final_env =
          D.add_term ctx' (D.add_bdim r' (D.resize_env (D.get_range env) restricted_env)) in
        let final_tp = eval mot final_env in
        let ext =
          D.Ext
            {var = i;
             dom = D.Clos {term = dom; env = restricted_env};
             mot = D.Clos2 {term = mot; env = restricted_env};
             ctx = ctx';
             varcase = D.Clos2 {term = varcase; env = restricted_env}}
        in
        D.Extent {tp = final_tp; term = D.Root ext}
    end
  | Syn.Gel (r, t) ->
    begin
      let r' = eval_bdim r env in
      match r' with
      | D.BVar i -> D.Gel (i, eval t (restrict_env r env))
    end
  | Syn.Engel (r, t) ->
    begin
      let r' = eval_bdim r env in
      match r' with
      | D.BVar i -> D.Engel (i, eval t (restrict_env r env))
    end
  | Syn.Ungel (mot, gel, case) ->
    let (l, env') = D.mk_bvar env in
    do_ungel
      (D.get_range env)
      (D.Clos {term = mot; env})
      l
      (eval gel env')
      (D.Clos {term = gel; env})
      (D.Clos {term = case; env})
