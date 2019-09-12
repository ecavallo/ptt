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
  | D.Neutral {term = e; _} ->
     let final_tp = do_clos tp n in
     D.Neutral {tp = final_tp; term = D.NRec (tp, zero, suc, e)}
  | _ -> raise (Nbe_failed "Not a number")

and do_fst p =
  match p with
  | D.Pair (p1, _) -> p1
  | D.Neutral {tp = D.Sg (t, _); term = ne} ->
     D.Neutral {tp = t; term = D.Fst ne}
  | _ -> raise (Nbe_failed "Couldn't fst argument in do_fst")

and do_snd p =
  match p with
  | D.Pair (_, p2) -> p2
  | D.Neutral {tp = D.Sg (_, clo); term = ne} ->
     let fst = do_fst p in
     D.Neutral {tp = do_clos clo fst; term = D.Snd ne}
  | _ -> raise (Nbe_failed "Couldn't snd argument in do_snd")

and do_bapp t r =
  match t with
  | D.BLam bclo -> do_bclos bclo r
  | D.Neutral {tp; term} ->
     begin
       match r with
       | D.BVar i ->
          begin
            match tp with
            | D.Bridge dst ->
               let dst = do_bclos dst r in
               D.Neutral {tp = dst; term = D.BApp (term, i)}
            | _ -> raise (Nbe_failed "Not a bridge in do_bapp")
          end
     end
  | _ -> raise (Nbe_failed "Not a bridge or neutral in bapp")

and do_j mot refl eq =
  match eq with
  | D.Refl t -> do_clos refl t
  | D.Neutral {tp; term} ->
     begin
       match tp with
       | D.Id (tp, left, right) ->
          D.Neutral
            { tp = do_clos3 mot left right eq;
              term = D.J (mot, refl, tp, left, right, term) }
       | _ -> raise (Nbe_failed "Not an Id in do_j")
     end
  | _ -> raise (Nbe_failed "Not a refl or neutral in do_j")

and do_extent r dom mot ctx varcase =
  match r with
  | D.BVar i ->
     D.Neutral
       {tp = do_bclosclos mot r ctx;
        term = D.Extent (i, dom, mot, ctx, varcase)}

and do_ap f a =
  match f with
  | D.Lam clos -> do_clos clos a
  | D.Neutral {tp; term = e} ->
     begin
       match tp with
       | D.Pi (src, dst) ->
          let dst = do_clos dst a in
          D.Neutral {tp = dst; term = D.Ap (e, D.Normal {tp = src; term = a})}
       | _ -> raise (Nbe_failed "Not a Pi in do_ap")
     end
  | _ -> raise (Nbe_failed "Not a function in do_ap")

and do_gel r t =
  match r with
  | D.BVar i -> D.Gel (i, t)

and do_engel r t =
  match r with
  | D.BVar i -> D.Engel (i, t)

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
    begin
      match t' with
      | D.Engel (_, t') -> t'
      | D.Neutral {tp; term = e} ->
        begin
          match tp with
          | D.Gel (_, dst) ->
            D.Neutral {tp = dst; term = D.Ungel (D.Abs {var = List.length env; ne = e})}
          | _ -> raise (Nbe_failed "Not a Gel in do_ungel")
        end
      | _ -> raise (Nbe_failed "Not a term of Gel in do_ungel")
    end
     
let rec read_back_nf env nf =
  match nf with
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
  | D.Normal {tp = D.Neutral _; term = D.Neutral {term = ne; _}} -> read_back_ne env ne
  | _ -> raise (Nbe_failed "Ill-typed read_back_nf")

and read_back_tp env d =
  match d with
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

and read_back_ne env ne =
  match ne with
  | D.Var x -> Syn.Var (level_to_index env x)
  | D.Ap (ne, arg) ->
     Syn.Ap (read_back_ne env ne, read_back_nf env arg)
  | D.NRec (tp, zero, suc, n) ->
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
       read_back_ne env n)
  | D.Fst ne -> Syn.Fst (read_back_ne env ne)
  | D.Snd ne -> Syn.Snd (read_back_ne env ne)
  | D.BApp (ne, i) -> Syn.BApp (read_back_ne env ne, Syn.BVar (level_to_index env i))
  | D.Extent (i, dom, mot, ctx, varcase) ->
    let i' = level_to_index env i in
    let i_dom = do_bclos dom (D.BVar i) in
    let ctx' = read_back_nf env (D.Normal {tp = i_dom; term = ctx}) in
    begin
      match Syn.extract_bvar i' ctx' with
      | Some extract ->
        let extract_lam = D.BLam (D.Clos {term = extract; env = env}) in
        let output_ty = do_bclosclos mot (D.BVar i) ctx in
        let output_varcase = do_closbclos varcase extract_lam (D.BVar i) in
        read_back_nf env (D.Normal {tp = output_ty; term = output_varcase})
      | None ->
        let dim_var = D.mk_bvar env in
        let applied_dom = do_bclos dom dim_var in
        let dom' = read_back_tp (D.BDim dim_var :: env) applied_dom in
        let dom_var = D.mk_var applied_dom (D.BDim dim_var :: env) in
        let applied_mot = do_bclosclos mot dim_var dom_var in
        let mot' = read_back_tp (D.Term applied_dom :: D.BDim dim_var :: env) applied_mot in
        let varcase_bridge = D.mk_var (D.Bridge dom) env in
        let varcase_dim = D.mk_bvar (D.Term varcase_bridge :: env) in
        let varcase_inst = do_bapp varcase_bridge varcase_dim in
        let varcase_mot = do_bclosclos mot varcase_dim varcase_inst in
        let applied_varcase = do_closbclos varcase varcase_bridge varcase_dim in
        let varcase' =
          read_back_nf
            (D.BDim varcase_dim :: D.Term varcase_bridge :: env)
            (D.Normal {tp = varcase_mot; term = applied_varcase}) in
        Syn.Extent (Syn.BVar (level_to_index env i), dom', mot', ctx', varcase')
    end
  | D.J (mot, refl, tp, left, right, eq) ->
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
    let eq_syn = read_back_ne env eq in
    Syn.J (mot_syn, refl_syn, eq_syn)
  | D.Ungel (Abs {var; ne}) ->
    let var' = D.mk_bvar env in
    let ne' = D.subst_bvar_ne (List.length env) var ne in
    Syn.Ungel (read_back_ne (D.BDim var' :: env) ne')

let rec check_nf env nf1 nf2 =
  match nf1, nf2 with
  (* Functions *)
  | D.Normal {tp = D.Pi (src1, dest1); term = f1},
    D.Normal {tp = D.Pi (_, dest2); term = f2} ->
    let arg = D.mk_var src1 env in
    let nf1 = D.Normal {tp = do_clos dest1 arg; term = do_ap f1 arg} in
    let nf2 = D.Normal {tp = do_clos dest2 arg; term = do_ap f2 arg} in
    check_nf (D.Term arg :: env) nf1 nf2
  (* Pairs *)
  | D.Normal {tp = D.Sg (fst1, snd1); term = p1},
    D.Normal {tp = D.Sg (fst2, snd2); term = p2} ->
    let p11, p21 = do_fst p1, do_fst p2 in
    let snd1 = do_clos snd1 p11 in
    let snd2 = do_clos snd2 p21 in
    let p12, p22 = do_snd p1, do_snd p2 in
    check_nf env (D.Normal {tp = fst1; term = p11}) (D.Normal {tp = fst2; term = p21})
    && check_nf env (D.Normal {tp = snd1; term = p12}) (D.Normal {tp = snd2; term = p22})
  (* Numbers *)
  | D.Normal {tp = D.Nat; term = D.Zero},
    D.Normal {tp = D.Nat; term = D.Zero} -> true
  | D.Normal {tp = D.Nat; term = D.Suc nf1},
    D.Normal {tp = D.Nat; term = D.Suc nf2} ->
    check_nf env (D.Normal {tp = D.Nat; term = nf1}) (D.Normal {tp = D.Nat; term = nf2})
  | D.Normal {tp = D.Nat; term = D.Neutral {term = ne1; _}},
    D.Normal {tp = D.Nat; term = D.Neutral {term = ne2; _}}-> check_ne env ne1 ne2
  (* Id *)
  | D.Normal {tp = D.Id (tp, _, _); term = D.Refl term1},
    D.Normal {tp = D.Id (_, _, _); term = D.Refl term2} ->
    check_nf env (D.Normal {tp; term = term1}) (D.Normal {tp; term = term2})
  | D.Normal {tp = D.Id _; term = D.Neutral {term = term1; _}},
    D.Normal {tp = D.Id _; term = D.Neutral {term = term2; _}} ->
    check_ne env term1 term2
  (* Bridge *)
  | D.Normal {tp = D.Bridge dest1; term = p1},
    D.Normal {tp = D.Bridge dest2; term = p2} ->
    let arg = D.mk_bvar env in
    let nf1 = D.Normal {tp = do_bclos dest1 arg; term = do_bapp p1 arg} in
    let nf2 = D.Normal {tp = do_bclos dest2 arg; term = do_bapp p2 arg} in
    check_nf (D.BDim arg :: env) nf1 nf2
  (* Gel *)
  | D.Normal {tp = D.Gel (_, tp1); term = D.Engel (_, t1)},
    D.Normal {tp = D.Gel (_, tp2); term = D.Engel (_, t2)} ->
    check_nf env (D.Normal {tp = tp1; term = t1}) (D.Normal {tp = tp2; term = t2})
  | D.Normal {tp = D.Gel (_, tp1); term = D.Engel (_, t1)},
    D.Normal {tp = D.Gel (i2, _); term = D.Neutral {term = g2; _}} ->
    (* is there a more efficient way? *)
    let i2' = level_to_index env i2 in
    let g2' = read_back_ne env g2 in
    begin
      match Syn.extract_bvar i2' g2' with
      | Some extract ->
        read_back_nf env (D.Normal {tp = tp1; term = t1}) = Syn.Ungel extract
      | None -> false
    end
  | D.Normal {tp = D.Gel (i1, _); term = D.Neutral {term = g1; _}},
    D.Normal {tp = D.Gel (_, tp2); term = D.Engel (_, t2)} ->
    (* is there a more efficient way? *)
    let i1' = level_to_index env i1 in
    let g1' = read_back_ne env g1 in
    begin
      match Syn.extract_bvar i1' g1' with
      | Some extract ->
        Syn.Ungel extract = read_back_nf env (D.Normal {tp = tp2; term = t2})
      | None -> false
    end
  | D.Normal {tp = D.Gel _; term = D.Neutral {term = g1; _}},
    D.Normal {tp = D.Gel _; term = D.Neutral {term = g2; _}} ->
    check_ne env g1 g2
  (* Types *)
  | D.Normal {tp = D.Uni _; term = t1}, D.Normal {tp = D.Uni _; term = t2} ->
     check_tp ~subtype:false env t1 t2
  (* Extent type on the left *)
  | D.Normal {tp = D.Neutral {term = tp1; _}; term = term1}, _ ->
    begin
      match try_extent env tp1 with
      | Some (tp1, _) -> check_nf env (D.Normal {tp = tp1; term = term1}) nf2
      | None -> check_ne_wrapped env nf1 nf2
    end
  (* Extent type on the right *)
  | _, D.Normal {tp = D.Neutral {term = tp2; _}; term = term2} ->
    begin
      match try_extent env tp2 with
      | Some (tp2, _) -> check_nf env nf1 (D.Normal {tp = tp2; term = term2})
      | None -> check_ne_wrapped env nf1 nf2
    end
  | _ -> check_ne_wrapped env nf1 nf2

and check_ne env ne1 ne2 =
  (* First try to reduce instances of extent *)
  match try_extent env ne1 with
  | Some (term1, tp) ->
     check_nf env
       (D.Normal {term = term1; tp})
       (D.Normal {term = D.Neutral {tp; term = ne2}; tp})
  | None ->
    begin
      match try_extent env ne2 with
      | Some (term2, tp) ->
        check_nf env
          (D.Normal {term = D.Neutral {tp; term = ne1}; tp})
          (D.Normal {term = term2; tp}) 
      | None -> check_ne_inner env ne1 ne2
    end

and check_ne_wrapped env nf1 nf2 =
  match nf1, nf2 with
  | D.Normal {tp = D.Neutral _; term = D.Neutral {term = ne1; _}},
    D.Normal {tp = D.Neutral _; term = D.Neutral {term = ne2; _}} -> check_ne env ne1 ne2
  | _ -> false

and check_ne_inner env ne1 ne2 =
  match ne1, ne2 with
  | D.Var x, D.Var y -> x = y
  | D.Ap (ne1, arg1), D.Ap (ne2, arg2) ->
    check_ne env ne1 ne2 && check_nf env arg1 arg2
  | D.NRec (tp1, zero1, suc1, n1), D.NRec (tp2, zero2, suc2, n2) ->
    let tp_var = D.mk_var D.Nat env in
    let applied_tp1 = do_clos tp1 tp_var in
    let applied_tp2 = do_clos tp2 tp_var in
    let zero_tp = do_clos tp1 D.Zero in
    let applied_suc_tp = do_clos tp1 (D.Suc tp_var) in
    let suc_var1 = D.mk_var applied_tp1 (D.Term tp_var :: env) in
    let suc_var2 = D.mk_var applied_tp2 (D.Term tp_var :: env) in
    let applied_suc1 = do_clos2 suc1 tp_var suc_var1 in
    let applied_suc2 = do_clos2 suc2 tp_var suc_var2 in
    check_tp ~subtype:false (D.Term tp_var :: env) applied_tp1 applied_tp2 &&
    check_nf env (D.Normal {tp = zero_tp; term = zero1}) (D.Normal {tp = zero_tp; term = zero2}) &&
    check_nf (D.Term suc_var1 :: D.Term tp_var :: env)
      (D.Normal {tp = applied_suc_tp; term = applied_suc1})
      (D.Normal {tp = applied_suc_tp; term = applied_suc2}) &&
    check_ne env n1 n2
  | D.Fst ne1, D.Fst ne2  -> check_ne env ne1 ne2
  | D.Snd ne1, D.Snd ne2 -> check_ne env ne1 ne2
  | D.BApp (ne1, i1), D.BApp (ne2, i2) -> check_ne env ne1 ne2 && i1 = i2
  | D.Extent (i1, dom1, mot1, ctx1, varcase1),
    D.Extent (i2, dom2, mot2, ctx2, varcase2) ->
    i1 = i2 &&
    let dim_var = D.mk_bvar env in
    let applied_dom1 = do_bclos dom1 dim_var in
    let applied_dom2 = do_bclos dom2 dim_var in
    check_tp ~subtype:false (D.BDim dim_var :: env) applied_dom1 applied_dom2 &&
    let dom_var = D.mk_var applied_dom1 (D.BDim dim_var :: env) in
    let applied_mot1 = do_bclosclos mot1 dim_var dom_var in
    let applied_mot2 = do_bclosclos mot2 dim_var dom_var in
    check_tp ~subtype:false (D.Term dom_var :: D.BDim dim_var :: env) applied_mot1 applied_mot2 &&
    let i_dom = do_bclos dom1 (D.BVar i1) in
    check_nf env (D.Normal {tp = i_dom; term = ctx1}) (D.Normal {tp = i_dom; term = ctx2}) &&
    let varcase_bridge = D.mk_var (D.Bridge dom1) env in
    let varcase_dim = D.mk_bvar (D.Term varcase_bridge :: env) in
    let varcase_inst = do_bapp varcase_bridge varcase_dim in
    let varcase_mot = do_bclosclos mot1 varcase_dim varcase_inst in
    let applied_varcase1 = do_closbclos varcase1 varcase_bridge varcase_dim in
    let applied_varcase2 = do_closbclos varcase2 varcase_bridge varcase_dim in
    check_nf (D.BDim varcase_dim :: D.Term varcase_bridge :: env)
      (D.Normal {tp = varcase_mot; term = applied_varcase1})
      (D.Normal {tp = varcase_mot; term = applied_varcase2})
  | D.J (mot1, refl1, tp1, left1, right1, eq1),
    D.J (mot2, refl2, tp2, left2, right2, eq2) ->
    check_tp ~subtype:false env tp1 tp2 &&
    check_nf env (D.Normal {tp = tp1; term = left1}) (D.Normal {tp = tp2; term = left2}) &&
    check_nf env (D.Normal {tp = tp1; term = right1}) (D.Normal {tp = tp2; term = right2}) &&
    let mot_var1 = D.mk_var tp1 env in
    let mot_var2 = D.mk_var tp1 (D.Term mot_var1 :: env) in
    let mot_var3 = D.mk_var (D.Id (tp1, left1, right1)) (D.Term mot_var2 :: D.Term mot_var1 :: env) in
    check_tp ~subtype:false (D.Term mot_var3 :: D.Term mot_var2 :: D.Term mot_var1 :: env)
      (do_clos3 mot1 mot_var1 mot_var2 mot_var3)
      (do_clos3 mot2 mot_var1 mot_var2 mot_var3) &&
    let refl_var = D.mk_var tp1 env in
    check_nf
      (D.Term refl_var :: env)
      (D.Normal
        {term = do_clos refl1 refl_var;
         tp = do_clos3 mot1 refl_var refl_var (D.Refl refl_var)})
      (D.Normal
        {term = do_clos refl2 refl_var;
         tp = do_clos3 mot2 refl_var refl_var (D.Refl refl_var)}) &&
    check_ne env eq1 eq2
  | D.Ungel (Abs {var = var1; ne = ne1}), D.Ungel (Abs {var = var2; ne = ne2}) ->
    let var = D.mk_bvar env in
    let ne1' = D.subst_bvar_ne (List.length env) var1 ne1 in
    let ne2' = D.subst_bvar_ne (List.length env) var2 ne2 in
    check_ne (D.BDim var :: env) ne1' ne2'
  | _ -> false

and check_tp ~subtype env d1 d2 =
  match d1, d2 with
  | D.Neutral {term = term1; _}, D.Neutral {term = term2; _} ->
    check_ne env term1 term2
  | D.Nat, D.Nat -> true
  | D.Id (tp1, left1, right1), D.Id (tp2, left2, right2) ->
    check_tp ~subtype env tp1 tp2 &&
    check_nf env (D.Normal {tp = tp1; term = left1}) (D.Normal {tp = tp1; term = left2}) &&
    check_nf env (D.Normal {tp = tp1; term = right1}) (D.Normal {tp = tp1; term = right2})
  | D.Pi (src, dest), D.Pi (src', dest') ->
    let var = D.mk_var src' env in
    check_tp ~subtype env src' src &&
    check_tp ~subtype (D.Term var :: env) (do_clos dest var) (do_clos dest' var)
  | D.Sg (fst, snd), D.Sg (fst', snd') ->
    let var = D.mk_var fst env in
    check_tp ~subtype env fst fst' &&
    check_tp ~subtype (D.Term var :: env) (do_clos snd var) (do_clos snd' var)
  | D.Bridge dest, D.Bridge dest' ->
    let var = D.mk_bvar env in
    check_tp ~subtype (D.BDim var :: env) (do_bclos dest var) (do_bclos dest' var)
  | D.Gel (i, t), D.Gel (i', t') ->
    i = i' && check_tp ~subtype env t t'
  | D.Uni k, D.Uni j -> if subtype then k <= j else k = j
  | _ -> false

and try_extent env = function
  | D.Extent (i, dom, mot, ctx, varcase) ->
    let i' = level_to_index env i in
    let i_dom = do_bclos dom (D.BVar i) in
    let ctx' = read_back_nf env (D.Normal {tp = i_dom; term = ctx}) in
    begin
      match Syn.extract_bvar i' ctx' with
      | Some extract ->
        let extract_lam = D.BLam (D.Clos {term = extract; env = env}) in
        let output_ty = do_bclosclos mot (D.BVar i) ctx in
        let output_varcase = do_closbclos varcase extract_lam (D.BVar i) in
        Some (output_varcase, output_ty)
      | None -> None
    end
  | _ -> None

