(* This file implements the normalization procedure. In addition the "unary" quotation
 * algorithm described by the paper, we also implement a binary operation for increased
 * efficiency. *)
module Syn = Syntax

module D = Domain

exception Nbe_failed of string

let level_to_index size i = List.length size - (i + 1)

let eval_bdim r (env : D.env) =
  match r with
  | Syn.BVar i ->
    begin
      match List.nth env i with
      | D.BDim s -> s
      | D.Term _ -> raise (Nbe_failed "Not a dimension term")
    end

(* TODO organize these closure functions in a better way *)

let rec do_bclos clo r =
  match clo with
  | D.Clos {term; env} -> eval term (D.BDim r :: env)
  | D.ConstClos t -> t

and do_clos clo a =
  match clo with
  | D.Clos {term; env} -> eval term (D.Term a :: env)
  | D.ConstClos t -> t

and do_clos2 (D.Clos2 {term; env}) a1 a2 =
  eval term (D.Term a2 :: D.Term a1 :: env)

and do_bclosclos (D.Clos2 {term; env}) r a =
  eval term (D.Term a :: D.BDim r :: env)

and do_closbclos (D.Clos2 {term; env}) a r =
  eval term (D.BDim r :: D.Term a :: env)

and do_clos3 (D.Clos3 {term; env}) a1 a2 a3 =
  eval term (D.Term a3 :: D.Term a2 :: Term a1 :: env)

and do_rec tp zero suc n =
  match n with
  | D.Zero -> zero
  | D.Suc n -> do_clos2 suc n (do_rec tp zero suc n)
  | D.Neutral {term = (x, stack); _} ->
     let final_tp = do_clos tp n in
     D.Neutral {tp = final_tp; term = (x, D.NRec (tp, zero, suc) :: stack)}
  | _ -> raise (Nbe_failed "Not a number")

and do_fst p =
  match p with
  | D.Pair (p1, _) -> p1
  | D.Neutral {tp = D.Sg (t, _); term = (x, stack)} ->
     D.Neutral {tp = t; term = (x, D.Fst :: stack)}
  | _ -> raise (Nbe_failed "Couldn't fst argument in do_fst")

and do_snd p =
  match p with
  | D.Pair (_, p2) -> p2
  | D.Neutral {tp = D.Sg (_, clo); term = (x, stack)} ->
     let fst = do_fst p in
     D.Neutral {tp = do_clos clo fst; term = (x, D.Snd :: stack)}
  | _ -> raise (Nbe_failed "Couldn't snd argument in do_snd")

and do_bapp t r =
  match t with
  | D.BLam bclo -> do_bclos bclo r
  | D.Neutral {tp; term = (x, stack)} ->
     begin
       match r with
       | D.BVar i ->
          begin
            match tp with
            | D.Bridge dst ->
               let dst = do_bclos dst r in
               D.Neutral {tp = dst; term = (x, D.BApp i :: stack)}
            | _ -> raise (Nbe_failed "Not a bridge in do_bapp")
          end
     end
  | _ -> raise (Nbe_failed "Not a bridge or neutral in bapp")

and do_j mot refl eq =
  match eq with
  | D.Refl t -> do_clos refl t
  | D.Neutral {tp; term = (x, stack)} ->
     begin
       match tp with
       | D.Id (tp, left, right) ->
          D.Neutral
            { tp = do_clos3 mot left right eq;
              term = (x, D.J (mot, refl, tp, left, right) :: stack) }
       | _ -> raise (Nbe_failed "Not an Id in do_j")
     end
  | _ -> raise (Nbe_failed "Not a refl or neutral in do_j")

and do_extent r dom mot ctx varcase =
  match r with
  | D.BVar var ->
    D.Extent {var; dom; mot; ctx; varcase; stack = []}

and do_ap f a =
  match f with
  | D.Lam clos -> do_clos clos a
  | D.Neutral {tp; term = (x, stack)} ->
    begin
      match tp with
      | D.Pi (src, dst) ->
        let dst = do_clos dst a in
        D.Neutral {tp = dst; term = (x, D.Ap (D.Normal {tp = src; term = a}) :: stack)}
      | _ -> raise (Nbe_failed "Not a Pi in do_ap")
    end
  | _ -> raise (Nbe_failed "Not a function in do_ap")

and do_gel r t =
  match r with
  | D.BVar i -> D.Gel (i, t)

and do_engel r t =
  match r with
  | D.BVar i -> D.Engel (i, t)

and do_ungel env t =
  begin
    match t with
    | D.Engel (_, t) -> t
    | D.Neutral {tp; term = (x, stack)} ->
      begin
        match tp with
        | D.Gel (_, dst) ->
          D.Neutral {tp = dst; term = (x, D.Ungel env :: stack)}
        | _ -> raise (Nbe_failed "Not a Gel in do_ungel")
      end
    | _ -> raise (Nbe_failed "Not a term of Gel in do_ungel")
  end

and eval t (env : D.env) =
  match t with
  | Syn.Var i ->
     begin
       match List.nth env i with
       | D.Term t -> t
       | D.BDim _-> raise (Nbe_failed "Not a term variable")
     end
  | Syn.Let (def, body) -> eval body (Term (eval def env) :: env)
  | Syn.Check (term, _) -> eval term env
  | Syn.Nat -> D.Nat
  | Syn.Zero -> D.Zero
  | Syn.Suc t -> D.Suc (eval t env)
  | Syn.NRec (tp, zero, suc, n) ->
     do_rec
       (Clos {term = tp; env})
       (eval zero env)
       (Clos2 {term = suc; env})
       (eval n env)
  | Syn.Pi (src, dest) ->
    D.Pi (eval src env, (Clos {term = dest; env}))
  | Syn.Lam t -> D.Lam (Clos {term = t; env})
  | Syn.Ap (t1, t2) -> do_ap (eval t1 env) (eval t2 env)
  | Syn.Uni i -> D.Uni i
  | Syn.Sg (t1, t2) -> D.Sg (eval t1 env, (Clos {term = t2; env}))
  | Syn.Pair (t1, t2) -> D.Pair (eval t1 env, eval t2 env)
  | Syn.Fst t -> do_fst (eval t env)
  | Syn.Snd t -> do_snd (eval t env)
  | Syn.Bridge dest -> D.Bridge (Clos {term = dest; env})
  | Syn.BApp (t,r) -> do_bapp (eval t env) (eval_bdim r env)
  | Syn.BLam t -> D.BLam (Clos {term = t; env})
  | Syn.Refl t -> D.Refl (eval t env)
  | Syn.Id (tp, left, right) -> D.Id (eval tp env, eval left env, eval right env)
  | Syn.J (mot, refl, eq) ->
    do_j (D.Clos3 {term = mot; env}) (D.Clos {term = refl; env}) (eval eq env)
  | Syn.Extent (r, dom, mot, ctx, varcase) ->
    do_extent
      (eval_bdim r env)
      (D.Clos {term = dom; env})
      (D.Clos2 {term = mot; env})
      (eval ctx env)
      (D.Clos2 {term = varcase; env})
  | Syn.Gel (r, t) -> do_gel (eval_bdim r env) (eval t env)
  | Syn.Engel (r, t) -> do_engel (eval_bdim r env) (eval t env)
  | Syn.Ungel t ->
    let var = D.mk_bvar env in
    let t' = eval t (D.BDim var :: env) in
    do_ungel env t'

let rec apply_stack env t0 = function
  | [] -> t0
  | D.Ap (Normal {term;_}) :: stack -> do_ap (apply_stack env t0 stack) term
  | D.NRec (tp, zero, suc) :: stack -> do_rec tp zero suc (apply_stack env t0 stack)
  | D.Fst :: stack -> do_fst (apply_stack env t0 stack)
  | D.Snd :: stack -> do_snd (apply_stack env t0 stack)
  | D.BApp i :: stack -> do_bapp (apply_stack env t0 stack) (D.BVar i)
  | D.J (mot, refl, _, _, _) :: stack -> do_j mot refl (apply_stack env t0 stack)
  | D.Ungel env :: stack -> do_ungel env (apply_stack env t0 stack)

let rec reduce_extent env term =
  match term with
  | D.Extent {var = i; dom; ctx; varcase; stack; _} ->
    let inner_env = D.stack_env env stack in
    let i' = level_to_index inner_env i in
    let i_dom = do_bclos dom (D.BVar i) in
    let ctx' = read_back_nf inner_env (D.Normal {tp = i_dom; term = ctx}) in
    begin
      match Syn.extract_bvar i' ctx' with
      | Some extract ->
        let extract_lam = D.BLam (D.Clos {term = extract; env = inner_env}) in
        let output_varcase = do_closbclos varcase extract_lam (D.BVar i) in
        reduce_extent env (apply_stack env output_varcase stack)
      | None -> term
    end
  | _ -> term

and reduce_extent_nf env (D.Normal {tp; term}) =
  D.Normal {tp = reduce_extent env tp; term = reduce_extent env term}

and read_back_nf env nf =
  match reduce_extent_nf env nf with
  (* Functions *)
  | D.Normal {tp = D.Pi (src, dest); term = f} ->
     let arg = D.mk_var src env in
     let nf = D.Normal {tp = do_clos dest arg; term = do_ap f arg} in
     Syn.Lam (read_back_nf (D.Term arg :: env) nf)
  (* Pairs *)
  | D.Normal {tp = D.Sg (fst, snd); term = p} ->
     let fst' = do_fst p in
     let snd = do_clos snd fst' in
     let snd' = do_snd p in
     Syn.Pair
       (read_back_nf env (D.Normal { tp = fst; term = fst'}),
        read_back_nf env (D.Normal { tp = snd; term = snd'}))
  (* Numbers *)
  | D.Normal {tp = D.Nat; term = D.Zero} -> Syn.Zero
  | D.Normal {tp = D.Nat; term = D.Suc nf} ->
     Syn.Suc (read_back_nf env (D.Normal {tp = D.Nat; term = nf}))
  | D.Normal {tp = D.Nat; term = D.Neutral {term = ne; _}} -> read_back_ne env ne
  (* Bridge *)
  | D.Normal {tp = D.Bridge dest; term} ->
     let arg = D.mk_bvar env in
     let nf = D.Normal {tp = do_bclos dest arg; term = do_bapp term arg} in
     Syn.BLam (read_back_nf (D.BDim arg :: env) nf)
  (* Id *)
  | D.Normal {tp = D.Id (tp, _, _); term = D.Refl term} ->
     Syn.Refl (read_back_nf env (D.Normal {tp; term}))
  | D.Normal {tp = D.Id _; term = D.Neutral {term; _}} ->
     read_back_ne env term
  (* Gel *)
  | D.Normal {tp = D.Gel (_, tp); term = D.Engel (i, t)} ->
    let i' = level_to_index env i in
    Syn.Engel (Syn.BVar i', read_back_nf env (D.Normal {tp; term = t}))
  | D.Normal {tp = D.Gel (i, _); term = D.Neutral {term = g; _}} ->
    let i' = level_to_index env i in
    let g' = read_back_ne env g in
    begin
      match Syn.extract_bvar i' g' with
      | Some extract -> Syn.Engel (Syn.BVar i', Syn.Ungel extract)
      | None -> g'
    end
  (* Types *)
  | D.Normal {tp = D.Uni _; term = t} -> read_back_tp env t
  (* Irreducible extent term *)
  | D.Normal {tp = _; term = D.Extent {var = i; dom; mot; ctx; varcase; stack}} ->
    let inner_env = D.stack_env env stack in
    let dim_var = D.mk_bvar inner_env in
    let applied_dom = do_bclos dom dim_var in
    let dom' = read_back_tp (D.BDim dim_var :: inner_env) applied_dom in
    let dom_var = D.mk_var applied_dom (D.BDim dim_var :: inner_env) in
    let applied_mot = do_bclosclos mot dim_var dom_var in
    let mot' = read_back_tp (D.Term applied_dom :: D.BDim dim_var :: inner_env) applied_mot in
    let i_dom = do_bclos dom (D.BVar i) in
    let ctx' = read_back_nf inner_env (D.Normal {tp = i_dom; term = ctx}) in
    let varcase_bridge = D.mk_var (D.Bridge dom) inner_env in
    let varcase_dim = D.mk_bvar (D.Term varcase_bridge :: inner_env) in
    let varcase_inst = do_bapp varcase_bridge varcase_dim in
    let varcase_mot = do_bclosclos mot varcase_dim varcase_inst in
    let applied_varcase = do_closbclos varcase varcase_bridge varcase_dim in
    let varcase' =
      read_back_nf
        (D.BDim varcase_dim :: D.Term varcase_bridge :: inner_env)
        (D.Normal {tp = varcase_mot; term = applied_varcase})
    in
    read_back_stack env
      (Syn.Extent (Syn.BVar (level_to_index inner_env i), dom', mot', ctx', varcase'))
      stack
  (* Neutral *)
  | D.Normal {tp = _; term = D.Neutral {term = ne; _}} -> read_back_ne env ne
  | _ -> raise (Nbe_failed "Ill-typed read_back_nf")

and read_back_tp env d =
  match reduce_extent env d with
  | D.Neutral {term; _} -> read_back_ne env term
  | D.Nat -> Syn.Nat
  | D.Pi (src, dest) ->
     let var = D.mk_var src env in
     Syn.Pi (read_back_tp env src, read_back_tp (D.Term var :: env) (do_clos dest var))
  | D.Sg (fst, snd) ->
     let var = D.mk_var fst env in
     Syn.Sg (read_back_tp env fst, read_back_tp (D.Term var :: env) (do_clos snd var))
  | D.Bridge dest ->
     let var = D.mk_bvar env in
     Syn.Bridge (read_back_tp (D.BDim var :: env) (do_bclos dest var))
  | D.Id (tp, left, right) ->
     Syn.Id
       (read_back_tp env tp,
        read_back_nf env (D.Normal {tp; term = left}),
        read_back_nf env (D.Normal {tp; term = right}))
  | D.Gel (i, t) ->
    Syn.Gel (Syn.BVar (level_to_index env i), read_back_tp env t)
  | D.Uni k -> Syn.Uni k
  | _ -> raise (Nbe_failed "Not a type in read_back_tp")

and read_back_ne env (x, stack) =
  let inner_env = D.stack_env env stack in
  read_back_stack env (Syn.Var (level_to_index inner_env x)) stack

and read_back_stack env t0 = function
  | [] -> t0
  | D.Ap arg :: stack ->
    Syn.Ap (read_back_stack env t0 stack, read_back_nf env arg)
  | D.NRec (tp, zero, suc) :: stack ->
    let tp_var = D.mk_var D.Nat env in
    let applied_tp = do_clos tp tp_var in
    let zero_tp = do_clos tp D.Zero in
    let applied_suc_tp = do_clos tp (D.Suc tp_var) in
    let tp' = read_back_tp (D.Term tp_var :: env) applied_tp in
    let suc_var = D.mk_var applied_tp (D.Term tp_var :: env) in
    let applied_suc = do_clos2 suc tp_var suc_var in
    let suc' =
      read_back_nf
        (D.Term applied_tp :: D.Term tp_var :: env)
        (D.Normal {tp = applied_suc_tp; term = applied_suc}) in
    Syn.NRec
      (tp',
       read_back_nf env (D.Normal {tp = zero_tp; term = zero}),
       suc',
       read_back_stack env t0 stack)
  | D.Fst :: stack -> Syn.Fst (read_back_stack env t0 stack)
  | D.Snd :: stack -> Syn.Snd (read_back_stack env t0 stack)
  | D.BApp i :: stack -> Syn.BApp (read_back_stack env t0 stack, Syn.BVar (level_to_index env i))
  | D.J (mot, refl, tp, left, right) :: stack ->
    let mot_var1 = D.mk_var tp env in
    let mot_var2 = D.mk_var tp (D.Term mot_var1 :: env) in
    let mot_var3 = D.mk_var (D.Id (tp, left, right)) (D.Term mot_var2 :: D.Term mot_var1 :: env) in
    let mot_syn =
      read_back_tp
        (D.Term mot_var3 :: D.Term mot_var2 :: D.Term mot_var1 :: env)
        (do_clos3 mot mot_var1 mot_var2 mot_var3) in
    let refl_var = D.mk_var tp env in
    let refl_syn =
      read_back_nf
        (D.Term refl_var :: env)
        (D.Normal
           {term = do_clos refl refl_var;
            tp = do_clos3 mot refl_var refl_var (D.Refl refl_var)}) in
    Syn.J (mot_syn, refl_syn, read_back_stack env t0 stack)
  | D.Ungel env :: stack ->
    let var = D.mk_bvar env in
    Syn.Ungel (read_back_stack (D.BDim var :: env) t0 stack)

let rec check_nf env1 env2 nf1 nf2 =
  match reduce_extent_nf env1 nf1, reduce_extent_nf env2 nf2 with
  (* Functions *)
  | D.Normal {tp = D.Pi (src1, dest1); term = f1},
    D.Normal {tp = D.Pi (src2, dest2); term = f2} ->
    let arg1 = D.mk_var src1 env1 in
    let arg2 = D.mk_var src2 env2 in
    let nf1 = D.Normal {tp = do_clos dest1 arg1; term = do_ap f1 arg1} in
    let nf2 = D.Normal {tp = do_clos dest2 arg2; term = do_ap f2 arg2} in
    check_nf (D.Term arg1 :: env1) (D.Term arg2 :: env2) nf1 nf2
  (* Pairs *)
  | D.Normal {tp = D.Sg (fst1, snd1); term = p1},
    D.Normal {tp = D.Sg (fst2, snd2); term = p2} ->
    let p11, p21 = do_fst p1, do_fst p2 in
    let snd1 = do_clos snd1 p11 in
    let snd2 = do_clos snd2 p21 in
    let p12, p22 = do_snd p1, do_snd p2 in
    check_nf env1 env2 (D.Normal {tp = fst1; term = p11}) (D.Normal {tp = fst2; term = p21})
    && check_nf env1 env2 (D.Normal {tp = snd1; term = p12}) (D.Normal {tp = snd2; term = p22})
  (* Numbers *)
  | D.Normal {tp = D.Nat; term = D.Zero},
    D.Normal {tp = D.Nat; term = D.Zero} -> true
  | D.Normal {tp = D.Nat; term = D.Suc nf1},
    D.Normal {tp = D.Nat; term = D.Suc nf2} ->
    check_nf env1 env2 (D.Normal {tp = D.Nat; term = nf1}) (D.Normal {tp = D.Nat; term = nf2})
  | D.Normal {tp = D.Nat; term = D.Neutral {term = ne1; _}},
    D.Normal {tp = D.Nat; term = D.Neutral {term = ne2; _}}-> check_ne env1 env2 ne1 ne2
  (* Id *)
  | D.Normal {tp = D.Id (tp1, _, _); term = D.Refl term1},
    D.Normal {tp = D.Id (tp2, _, _); term = D.Refl term2} ->
    check_nf env1 env2 (D.Normal {tp = tp1; term = term1}) (D.Normal {tp = tp2; term = term2})
  | D.Normal {tp = D.Id _; term = D.Neutral {term = term1; _}},
    D.Normal {tp = D.Id _; term = D.Neutral {term = term2; _}} ->
    check_ne env1 env2 term1 term2
  (* Bridge *)
  | D.Normal {tp = D.Bridge dest1; term = p1},
    D.Normal {tp = D.Bridge dest2; term = p2} ->
    let arg1 = D.mk_bvar env1 in
    let arg2 = D.mk_bvar env2 in
    let nf1 = D.Normal {tp = do_bclos dest1 arg1; term = do_bapp p1 arg1} in
    let nf2 = D.Normal {tp = do_bclos dest2 arg2; term = do_bapp p2 arg2} in
    check_nf (D.BDim arg1 :: env1) (D.BDim arg2 :: env2) nf1 nf2
  (* Gel *)
  | D.Normal {tp = D.Gel (_, tp1); term = D.Engel (_, t1)},
    D.Normal {tp = D.Gel (_, tp2); term = D.Engel (_, t2)} ->
    check_nf env1 env2 (D.Normal {tp = tp1; term = t1}) (D.Normal {tp = tp2; term = t2})
  | D.Normal {tp = D.Gel (_, tp1); term = D.Engel (_, t1)},
    D.Normal {tp = D.Gel (i2, _); term = D.Neutral {term = g2; _}} ->
    (* todo: inefficient *)
    let i2' = level_to_index env2 i2 in
    let g2' = read_back_ne env2 g2 in
    begin
      match Syn.extract_bvar i2' g2' with
      | Some extract ->
        read_back_nf env1 (D.Normal {tp = tp1; term = t1}) = Syn.Ungel extract
      | None -> false
    end
  | D.Normal {tp = D.Gel (i1, _); term = D.Neutral {term = g1; _}},
    D.Normal {tp = D.Gel (_, tp2); term = D.Engel (_, t2)} ->
    (* todo: inefficient *)
    let i1' = level_to_index env1 i1 in
    let g1' = read_back_ne env1 g1 in
    begin
      match Syn.extract_bvar i1' g1' with
      | Some extract ->
        Syn.Ungel extract = read_back_nf env2 (D.Normal {tp = tp2; term = t2})
      | None -> false
    end
  | D.Normal {tp = D.Gel _; term = D.Neutral {term = g1; _}},
    D.Normal {tp = D.Gel _; term = D.Neutral {term = g2; _}} ->
    check_ne env1 env2 g1 g2
  (* Types *)
  | D.Normal {tp = D.Uni _; term = t1}, D.Normal {tp = D.Uni _; term = t2} ->
    check_tp ~subtype:false env1 env2 t1 t2
  (* Irreducible extent terms *)
  | D.Normal {term = D.Extent {var = i1; dom = dom1; mot = mot1; ctx = ctx1; varcase = varcase1; stack = stack1}; _},
    D.Normal {term = D.Extent {var = i2; dom = dom2; mot = mot2; ctx = ctx2; varcase = varcase2; stack = stack2}; _} ->
    check_extent env1 env2
      (i1, dom1, mot1, ctx1, varcase1, stack1)
      (i2, dom2, mot2, ctx2, varcase2, stack2)
  | D.Normal {tp = _; term = D.Neutral {term = ne1; _}},
    D.Normal {tp = _; term = D.Neutral {term = ne2; _}} ->
    check_ne env1 env2 ne1 ne2
  | _ -> false

and check_extent env1 env2 (i1, dom1, mot1, ctx1, varcase1, stack1) (i2, dom2, mot2, ctx2, varcase2, stack2) =
  let inner_env1 = D.stack_env env1 stack1 in
  let inner_env2 = D.stack_env env2 stack2 in
  level_to_index inner_env1 i1 = level_to_index inner_env2 i2 &&
  let dim_var1 = D.mk_bvar inner_env1 in
  let dim_var2 = D.mk_bvar inner_env2 in
  let applied_dom1 = do_bclos dom1 dim_var1 in
  let applied_dom2 = do_bclos dom2 dim_var2 in
  check_tp ~subtype:false
    (D.BDim dim_var1 :: inner_env1) (D.BDim dim_var2 :: inner_env2) applied_dom1 applied_dom2 &&
  let dom_var1 = D.mk_var applied_dom1 (D.BDim dim_var1 :: inner_env1) in
  let dom_var2 = D.mk_var applied_dom2 (D.BDim dim_var2 :: inner_env2) in
  let applied_mot1 = do_bclosclos mot1 dim_var1 dom_var1 in
  let applied_mot2 = do_bclosclos mot2 dim_var2 dom_var2 in
  check_tp ~subtype:false
    (D.Term applied_dom1 :: D.BDim dim_var1 :: inner_env1)
    (D.Term applied_dom2 :: D.BDim dim_var2 :: inner_env2)
    applied_mot1
    applied_mot2 &&
  let i_dom1 = do_bclos dom1 (D.BVar i1) in
  let i_dom2 = do_bclos dom2 (D.BVar i2) in
  check_nf inner_env1 inner_env2
    (D.Normal {tp = i_dom1; term = ctx1})
    (D.Normal {tp = i_dom2; term = ctx2}) &&
  let varcase1_bridge = D.mk_var (D.Bridge dom1) inner_env1 in
  let varcase2_bridge = D.mk_var (D.Bridge dom2) inner_env2 in
  let varcase1_dim = D.mk_bvar (D.Term varcase1_bridge :: inner_env1) in
  let varcase2_dim = D.mk_bvar (D.Term varcase2_bridge :: inner_env2) in
  let varcase1_inst = do_bapp varcase1_bridge varcase1_dim in
  let varcase2_inst = do_bapp varcase2_bridge varcase2_dim in
  let varcase1_mot = do_bclosclos mot1 varcase1_dim varcase1_inst in
  let varcase2_mot = do_bclosclos mot2 varcase2_dim varcase2_inst in
  let applied_varcase1 = do_closbclos varcase1 varcase1_bridge varcase1_dim in
  let applied_varcase2 = do_closbclos varcase2 varcase2_bridge varcase2_dim in
  check_nf
    (D.BDim varcase1_dim :: D.Term varcase1_bridge :: inner_env1)
    (D.BDim varcase2_dim :: D.Term varcase2_bridge :: inner_env2)
    (D.Normal {tp = varcase1_mot; term = applied_varcase1})
    (D.Normal {tp = varcase2_mot; term = applied_varcase2}) &&
  check_stack env1 env2 stack1 stack2

and check_ne env1 env2 (x1, stack1) (x2, stack2) =
  check_stack env1 env2 stack1 stack2 &&
  let inner_env1 = D.stack_env env1 stack1 in
  let inner_env2 = D.stack_env env2 stack2 in
  level_to_index inner_env1 x1 = level_to_index inner_env2 x2

and check_stack env1 env2 stack1 stack2 =
  match stack1, stack2 with
  | [], [] -> true
  | D.Ap arg1 :: stack1, D.Ap arg2 :: stack2 ->
    check_nf env1 env2 arg1 arg2 && check_stack env1 env2 stack1 stack2
  | D.NRec (tp1, zero1, suc1) :: stack1, D.NRec (tp2, zero2, suc2) :: stack2 ->
    let tp_var1 = D.mk_var D.Nat env1 in
    let tp_var2 = D.mk_var D.Nat env2 in
    let applied_tp1 = do_clos tp1 tp_var1 in
    let applied_tp2 = do_clos tp2 tp_var2 in
    let zero_tp1 = do_clos tp1 D.Zero in
    let zero_tp2 = do_clos tp2 D.Zero in
    let applied_suc_tp1 = do_clos tp1 (D.Suc tp_var1) in
    let applied_suc_tp2 = do_clos tp1 (D.Suc tp_var2) in
    let suc_var1 = D.mk_var applied_tp1 (D.Term tp_var1 :: env1) in
    let suc_var2 = D.mk_var applied_tp2 (D.Term tp_var2 :: env2) in
    let applied_suc1 = do_clos2 suc1 tp_var1 suc_var1 in
    let applied_suc2 = do_clos2 suc2 tp_var2 suc_var2 in
    check_tp ~subtype:false (D.Term tp_var1 :: env1) (D.Term tp_var2 :: env2) applied_tp1 applied_tp2 &&
    check_nf env1 env2 (D.Normal {tp = zero_tp1; term = zero1}) (D.Normal {tp = zero_tp2; term = zero2}) &&
    check_nf (D.Term suc_var1 :: D.Term tp_var1 :: env1) (D.Term suc_var2 :: D.Term tp_var2 :: env2)
      (D.Normal {tp = applied_suc_tp1; term = applied_suc1})
      (D.Normal {tp = applied_suc_tp2; term = applied_suc2}) &&
    check_stack env1 env2 stack1 stack2
  | D.Fst :: stack1, D.Fst :: stack2  -> check_stack env1 env2 stack1 stack2
  | D.Snd :: stack1, D.Snd :: stack2  -> check_stack env1 env2 stack1 stack2
  | D.BApp i1 :: stack1, D.BApp i2 :: stack2 ->
    level_to_index env1 i1 = level_to_index env2 i2
    && check_stack env1 env2 stack1 stack2
  | D.J (mot1, refl1, tp1, left1, right1) :: stack1,
    D.J (mot2, refl2, tp2, left2, right2) :: stack2 ->
    check_tp ~subtype:false env1 env2 tp1 tp2 &&
    check_nf env1 env2 (D.Normal {tp = tp1; term = left1}) (D.Normal {tp = tp2; term = left2}) &&
    check_nf env1 env2 (D.Normal {tp = tp1; term = right1}) (D.Normal {tp = tp2; term = right2}) &&
    let mot_var11 = D.mk_var tp1 env1 in
    let mot_var12 = D.mk_var tp2 env2 in
    let mot_var21 = D.mk_var tp1 (D.Term mot_var11 :: env1) in
    let mot_var22 = D.mk_var tp2 (D.Term mot_var12 :: env2) in
    let mot_var31 = D.mk_var (D.Id (tp1, left1, right1)) (D.Term mot_var21 :: D.Term mot_var11 :: env1) in
    let mot_var32 = D.mk_var (D.Id (tp2, left2, right2)) (D.Term mot_var22 :: D.Term mot_var12 :: env2) in
    check_tp ~subtype:false
      (D.Term mot_var31 :: D.Term mot_var21 :: D.Term mot_var11 :: env1)
      (D.Term mot_var32 :: D.Term mot_var22 :: D.Term mot_var12 :: env2)
      (do_clos3 mot1 mot_var11 mot_var21 mot_var31)
      (do_clos3 mot2 mot_var12 mot_var22 mot_var32) &&
    let refl_var1 = D.mk_var tp1 env1 in
    let refl_var2 = D.mk_var tp2 env2 in
    check_nf
      (D.Term refl_var1 :: env1)
      (D.Term refl_var2 :: env2)
      (D.Normal
        {term = do_clos refl1 refl_var1;
         tp = do_clos3 mot1 refl_var1 refl_var1 (D.Refl refl_var1)})
      (D.Normal
        {term = do_clos refl2 refl_var2;
         tp = do_clos3 mot2 refl_var2 refl_var2 (D.Refl refl_var2)}) &&
    check_stack env1 env2 stack1 stack2
  | D.Ungel env1 :: stack1, D.Ungel env2 :: stack2 ->
    let var1 = D.mk_bvar env1 in
    let var2 = D.mk_bvar env2 in
    check_stack (D.BDim var1 :: env1) (D.BDim var2 :: env2) stack1 stack2
  | _ -> false

and check_tp ~subtype env1 env2 d1 d2 =
  match reduce_extent env1 d1, reduce_extent env2 d2 with
  | D.Neutral {term = term1; _}, D.Neutral {term = term2; _} ->
    check_ne env1 env2 term1 term2
  | D.Extent {var = i1; dom = dom1; mot = mot1; ctx = ctx1; varcase = varcase1; stack = stack1},
    D.Extent {var = i2; dom = dom2; mot = mot2; ctx = ctx2; varcase = varcase2; stack = stack2} ->
    check_extent env1 env2
      (i1, dom1, mot1, ctx1, varcase1, stack1)
      (i2, dom2, mot2, ctx2, varcase2, stack2)
  | D.Nat, D.Nat -> true
  | D.Id (tp1, left1, right1), D.Id (tp2, left2, right2) ->
    check_tp ~subtype env1 env2 tp1 tp2 &&
    check_nf env1 env2 (D.Normal {tp = tp1; term = left1}) (D.Normal {tp = tp1; term = left2}) &&
    check_nf env1 env2 (D.Normal {tp = tp1; term = right1}) (D.Normal {tp = tp1; term = right2})
  | D.Pi (src1, dest1), D.Pi (src2, dest2) ->
    let var1 = D.mk_var src1 env1 in
    let var2 = D.mk_var src2 env2 in
    check_tp ~subtype env1 env2 src1 src2 &&
    check_tp ~subtype (D.Term var1 :: env1) (D.Term var2 :: env2)
      (do_clos dest1 var1)
      (do_clos dest2 var2)
  | D.Sg (fst1, snd1), D.Sg (fst2, snd2) ->
    let var1 = D.mk_var fst1 env1 in
    let var2 = D.mk_var fst2 env2 in
    check_tp ~subtype env1 env2 fst1 fst2 &&
    check_tp ~subtype (D.Term var1 :: env1) (D.Term var2 :: env2) (do_clos snd1 var1) (do_clos snd2 var2)
  | D.Bridge dest1, D.Bridge dest2 ->
    let var1 = D.mk_bvar env1 in
    let var2 = D.mk_bvar env2 in
    check_tp ~subtype (D.BDim var1 :: env1) (D.BDim var2 :: env2)
      (do_bclos dest1 var1)
      (do_bclos dest2 var2)
  | D.Gel (i1, t1), D.Gel (i2, t2) ->
    i1 = i2 && check_tp ~subtype env1 env2 t1 t2
  | D.Uni k, D.Uni j -> if subtype then k <= j else k = j
  | _ -> false
