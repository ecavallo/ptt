module Syn = Syntax
module D = Domain
module E = Eval

exception Quote_failed of string

let for_all2i f l1 l2 =
  let rec go i l1 l2 =
    match l1, l2 with
    | [], [] -> true
    | x1 :: l1, x2 :: l2 -> f i x1 x2 && go (i + 1) l1 l2
    | _ -> raise (Invalid_argument "for_all2i")
  in
  go 0 l1 l2

type env_entry =
  | BVar of D.lvl
  | Var of {level : D.lvl; tp : D.t}
  | Def of D.t
type env = env_entry list

let mk_bvar env size =
  (D.BVar size, BVar size :: env)

let mk_var tp env size =
  (D.Neutral {tp; term = D.root (D.Var size)}, Var {level = size; tp} :: env)

let mk_vars tps env size =
  (List.mapi (fun i tp -> D.Neutral {tp; term = D.root (D.Var (size + i))}) tps,
   List.rev_append
     (List.mapi (fun i tp -> Var {level = size + i; tp}) tps)
     env)

let env_to_sem_env env =
  let go = function
    | BVar i -> D.BDim (D.BVar i)
    | Var {level; tp} -> D.Term (D.Neutral {tp; term = D.root (D.Var level)})
    | Def term -> D.Term term
  in
  List.map go env

let read_back_level env x =
  let rec go acc = function
    | BVar i :: env -> if i = x then acc else go (acc + 1) env
    | Var {level; _} :: env -> if level = x then acc else go (acc + 1) env
    | Def _ :: env -> go (acc + 1) env
    | [] -> raise (Quote_failed "read back non-existent variable")
  in
  go 0 env

exception Cannot_reduce_extent

let rec reduce_extent_head env size ({var = i; dom; ctx; endcase; varcase; _} : D.extent_head) =
  let sem_env = env_to_sem_env env in
  let dom_i = E.do_bclos size dom (D.BVar i) in
  let i' = read_back_level env i in
  let ctx' = read_back_nf env size (D.Normal {tp = dom_i; term = ctx}) in
  begin
    match Syntax.unsubst_bvar i' ctx' with
    | Some extract ->
      let extract_ends =
        List.init (List.length endcase) (fun o -> E.eval extract (D.BDim (D.Const o) :: sem_env) size) in
      let extract_blam =
        D.BLam (D.Clos {term = extract; env = sem_env}) in
      let output_varcase = E.do_clos_extent size varcase extract_ends extract_blam (D.BVar i) in
      output_varcase
    | _ -> raise Cannot_reduce_extent
  end

and reduce_extent env size es =
  let rec go env size (e, s) =
    match s with
    | [] -> reduce_extent_head env size e
    | D.Ap (Normal {term;_}) :: s -> E.do_ap size (go env size (e, s)) term
    | D.NRec (tp, zero, suc) :: s -> E.do_rec size tp zero suc (go env size (e, s))
    | D.If (mot, tt, ff) :: s -> E.do_if size mot tt ff (go env size (e, s))
    | D.Fst :: s -> E.do_fst (go env size (e, s))
    | D.Snd :: s -> E.do_snd size (go env size (e, s))
    | D.BApp i :: s -> E.do_bapp size (go env size (e, s)) (D.BVar i)
    | D.J (mot, refl, _, _, _) :: s -> E.do_j size mot refl (go env size (e, s))
    | D.Ungel (_, _, mot, i, clo, case) :: s ->
      let es' = D.instantiate_spine D.instantiate_extent_head size i (e, s) in
      E.do_ungel size mot (go (BVar size :: env) (size + 1) es') clo case
  in
  try
    Some (go env size es)
  with
    Cannot_reduce_extent -> None

and read_back_nf env size nf =
  match nf with
  (* Functions *)
  | D.Normal {tp = D.Pi (src, dest); term = f} ->
    let (arg, arg_env) = mk_var src env size in
    let nf = D.Normal
        {tp = E.do_clos (size + 1) dest arg;
         term = E.do_ap (size + 1) f arg} in
    Syn.Lam (read_back_nf arg_env (size + 1) nf)
  (* Pairs *)
  | D.Normal {tp = D.Sg (fst, snd); term = p} ->
     let fst' = E.do_fst p in
     let snd = E.do_clos size snd fst' in
     let snd' = E.do_snd size p in
     Syn.Pair
       (read_back_nf env size (D.Normal {tp = fst; term = fst'}),
        read_back_nf env size (D.Normal {tp = snd; term = snd'}))
  (* Unit *)
  | D.Normal {tp = D.Unit; term = _} -> Syn.Triv
  (* Numbers *)
  | D.Normal {tp = D.Nat; term = D.Zero} -> Syn.Zero
  | D.Normal {tp = D.Nat; term = D.Suc nf} ->
     Syn.Suc (read_back_nf env size (D.Normal {tp = D.Nat; term = nf}))
  (* Booleans *)
  | D.Normal {tp = D.Bool; term = D.True} -> Syn.True
  | D.Normal {tp = D.Bool; term = D.False} -> Syn.False
  (* Bridge *)
  | D.Normal {tp = D.Bridge (dest, _); term} ->
     let (arg, arg_env) = mk_bvar env size in
     let nf = D.Normal
         {tp = E.do_bclos (size + 1) dest arg;
          term = E.do_bapp (size + 1) term arg} in
     Syn.BLam (read_back_nf arg_env (size + 1) nf)
  (* Id *)
  | D.Normal {tp = D.Id (tp, _, _); term = D.Refl term} ->
    Syn.Refl (read_back_nf env size (D.Normal {tp; term}))
  (* Gel *)
  | D.Normal {tp = D.Gel (_, endtps, rel); term = D.Engel (i, ts, t)} ->
    let i' = read_back_level env i in
    let applied_rel = E.do_closN size rel ts in
    Syn.Engel
      (Syn.BVar i',
       List.map2 (fun tp term -> read_back_nf env size (D.Normal {tp; term})) endtps ts,
       read_back_nf env size (D.Normal {tp = applied_rel; term = t}))
  (* Types *)
  | D.Normal {tp = D.Uni _; term = t} -> read_back_tp env size t
  (* Extent type *)
  | D.Normal {tp = D.Neutral {term = (D.Ext e, tp_spine); _}; term} ->
    begin
      match reduce_extent env size (e, tp_spine) with
      | Some tp -> read_back_nf env size (D.Normal {tp; term})
      | None -> read_back_quasi_ne env size term
    end
  | D.Normal {term; _} -> read_back_quasi_ne env size term

and read_back_tp env size d =
  match d with
  | D.Unit -> Syn.Unit
  | D.Nat -> Syn.Nat
  | D.Bool -> Syn.Bool
  | D.Pi (src, dest) ->
    let (arg, arg_env) = mk_var src env size in
    Syn.Pi (read_back_tp env size src, read_back_tp arg_env (size + 1) (E.do_clos (size + 1) dest arg))
  | D.Sg (fst, snd) ->
    let (arg, arg_env) = mk_var fst env size in
    Syn.Sg (read_back_tp env size fst, read_back_tp arg_env (size + 1) (E.do_clos (size + 1) snd arg))
  | D.Bridge (dest, endtps) ->
    let go o term =
      read_back_nf env size (D.Normal {tp = E.do_bclos size dest (D.Const o); term})
    in      
    let (arg, arg_env) = mk_bvar env size in
    Syn.Bridge (read_back_tp arg_env (size + 1) (E.do_bclos (size + 1) dest arg), List.mapi go endtps)
  | D.Id (tp, left, right) ->
    Syn.Id
      (read_back_tp env size tp,
       read_back_nf env size (D.Normal {tp; term = left}),
       read_back_nf env size (D.Normal {tp; term = right}))
  | D.Gel (i, endtps, rel) ->
    let i' = read_back_level env i in
    let (rel_args, rel_env) = mk_vars endtps env size in
    let rel_size = size + List.length endtps in
    Syn.Gel
      (Syn.BVar i',
       List.map (read_back_tp env size) endtps,
       read_back_tp rel_env rel_size (E.do_closN rel_size rel rel_args))
  | D.Uni k -> Syn.Uni k
  | _ -> read_back_quasi_ne env size d

and read_back_quasi_ne env size = function
  | D.Neutral {tp; term = (h, s)} ->
    begin
      match h with
      | D.Var _ -> read_back_ne env size (h, s)
      | D.Ext e ->
        begin
          match reduce_extent env size (e, s) with
          | Some term -> read_back_nf env size (D.Normal {tp; term})
          | None -> read_back_ne env size (h, s)
        end
    end
  | _ -> raise (Quote_failed "Ill-typed read_back_quasi_ne")

and read_back_ne env size (h, s) =
  match s with
  | [] ->
    begin
      match h with
      | D.Var i -> Syn.Var (read_back_level env i)
      | D.Ext e -> read_back_extent_head env size e
    end
  | D.Ap arg :: s ->
    Syn.Ap (read_back_ne env size (h, s), read_back_nf env size arg)
  | D.NRec (tp, zero, suc) :: s ->
    let (nat_arg, nat_env) = mk_var D.Nat env size in
    let applied_tp = E.do_clos (size + 1) tp nat_arg in
    let tp' = read_back_tp nat_env (size + 1) applied_tp in
    let zero_tp = E.do_clos size tp D.Zero in
    let zero' = read_back_nf env size (D.Normal {tp = zero_tp; term = zero}) in
    let (suc_arg, suc_env) = mk_var applied_tp nat_env (size + 1) in
    let applied_suc_tp = E.do_clos (size + 2) tp (D.Suc nat_arg) in
    let applied_suc = E.do_clos2 (size + 2) suc nat_arg suc_arg in
    let suc' = read_back_nf suc_env (size + 2) (D.Normal {tp = applied_suc_tp; term = applied_suc}) in
    Syn.NRec (tp', zero', suc', read_back_ne env size (h, s))
  | D.If (mot, tt, ff) :: s ->
    let (bool_arg, bool_env) = mk_var D.Bool env size in
    let applied_mot = E.do_clos (size + 1) mot bool_arg in
    let mot' = read_back_tp bool_env (size + 1) applied_mot in
    let tt_tp = E.do_clos size mot D.True in
    let tt' = read_back_nf env size (D.Normal {tp = tt_tp; term = tt}) in
    let ff_tp = E.do_clos size mot D.False in
    let ff' = read_back_nf env size (D.Normal {tp = ff_tp; term = ff}) in
    Syn.If (mot', tt', ff', read_back_ne env size (h, s))
  | D.Fst :: s -> Syn.Fst (read_back_ne env size (h, s))
  | D.Snd :: s -> Syn.Snd (read_back_ne env size (h, s))
  | D.BApp i :: s ->
    let i' = read_back_level env i in
    Syn.BApp (read_back_ne env size (h, s), Syn.BVar i')
  | D.J (mot, refl, tp, left, right) :: s ->
    let (mot_arg1, mot_env1) = mk_var tp env size in
    let (mot_arg2, mot_env2) = mk_var tp mot_env1 (size + 1) in
    let (mot_arg3, mot_env3) = mk_var (D.Id (tp, left, right)) mot_env2 (size + 2) in
    let mot_syn =
      read_back_tp mot_env3 (size + 3) (E.do_clos3 (size + 3) mot mot_arg1 mot_arg2 mot_arg3) in
    let (refl_arg, refl_env) = mk_var tp env size in
    let refl_syn =
      read_back_nf
        refl_env
        (size + 1)
        (D.Normal
           {term = E.do_clos (size + 1) refl refl_arg;
            tp = E.do_clos3 (size + 1) mot refl_arg refl_arg (D.Refl refl_arg)}) in
    Syn.J (mot_syn, refl_syn, read_back_ne env size (h, s))
  | D.Ungel (ends, rel, mot, i, _, case) :: s ->
    let width = List.length ends in
    let sem_env = env_to_sem_env env in
    let end_tps = List.map (function (D.Normal {tp; _}) -> tp) ends in
    let end_tms = List.map (function (D.Normal {term; _}) -> term) ends in
    let (end_args, _) = mk_vars end_tps env size in
    let applied_rel = E.do_closN size rel end_args in
    let mot_inner_env =
      D.Term applied_rel ::
      List.rev_append (List.map (fun t -> D.Term t) end_tps) sem_env in
    let mot_inner_tp =
      Syn.Gel (Syn.BVar 0, List.init width (fun o -> Syn.Var (o + 2)), Syn.Var (width + 1)) in
    let (mot_arg, mot_env) =
      mk_var (D.Bridge (D.Clos {term = mot_inner_tp; env = mot_inner_env}, end_tms)) env size in
    let mot' = read_back_tp mot_env (size + 1) (E.do_clos (size + 1) mot mot_arg) in
    let wit_rel = E.do_closN size rel end_tms in
    let (wit_arg, wit_env) = mk_var wit_rel env size in
    let engel_inner_env =
      D.Term wit_arg ::
      List.rev_append (List.map (fun t -> D.Term t) end_tms) sem_env in
    let engel_inner_tm =
      Syn.Engel (Syn.BVar 0, List.init width (fun o -> Syn.Var (o + 2)), Syn.Var 1) in
    let gel_term = D.BLam (D.Clos {term = engel_inner_tm; env = engel_inner_env}) in
    let case' = read_back_nf
        wit_env
        (size + 1)
        (D.Normal
           {term = E.do_clos (size + 1) case wit_arg;
            tp = E.do_clos (size + 1) mot gel_term}) in
    let ne' = D.instantiate_ne size i (h, s) in
    Syn.Ungel (List.length ends, mot', read_back_ne (BVar size :: env) (size + 1) ne', case')

and read_back_extent_head env size ({var = i; dom; mot; ctx; endcase; varcase} : D.extent_head) =
  let i' = read_back_level env i in
  let (barg, benv) = mk_bvar env size in
  let applied_dom = E.do_bclos (size + 1) dom barg in
  let dom' = read_back_tp benv (size + 1) applied_dom in
  let (dom_arg, dom_env) = mk_var applied_dom benv (size + 1) in
  let applied_mot = E.do_bclosclos (size + 2) mot barg dom_arg in
  let mot' = read_back_tp dom_env (size + 2) applied_mot in
  let dom_i = E.do_bclos size dom (D.BVar i) in
  let ctx' = read_back_nf env size (D.Normal {tp = dom_i; term = ctx}) in
  let endcase' =
    List.mapi
      (fun o case ->
         let case_dom = E.do_bclos size dom (D.Const o) in
         let (case_arg, case_env) = mk_var case_dom env size in
         let case_mot = E.do_bclosclos (size + 1) mot (D.Const o) case_arg in
         let applied_case = E.do_clos (size + 1) case case_arg in
         read_back_nf case_env (size + 1) (D.Normal {tp = case_mot; term = applied_case}))
      endcase in
  let width = List.length endcase in
  let endtps = E.do_consts size dom width in
  let (end_args, ends_env) = mk_vars endtps env size in
  let (bridge_arg, bridge_env) = mk_var (D.Bridge (dom, end_args)) ends_env (size + width) in
  let (varcase_barg, varcase_benv) = mk_bvar bridge_env (size + width + 1) in
  let varcase_inst = E.do_bapp (size + width + 2) bridge_arg varcase_barg in
  let varcase_mot = E.do_bclosclos (size + width + 2) mot varcase_barg varcase_inst in
  let applied_varcase = E.do_clos_extent (size + width + 2) varcase end_args bridge_arg varcase_barg in
  let varcase' =
    read_back_nf varcase_benv (size + width + 2) (D.Normal {tp = varcase_mot; term = applied_varcase})
  in
  Syn.Extent (Syn.BVar i', dom', mot', ctx', endcase', varcase')

let rec check_nf env size nf1 nf2 =
  match nf1, nf2 with
  (* Functions *)
  | D.Normal {tp = D.Pi (src1, dest1); term = f1},
    D.Normal {tp = D.Pi (_, dest2); term = f2} ->
    let (arg, arg_env) = mk_var src1 env size in
    let nf1 = D.Normal {tp = E.do_clos (size + 1) dest1 arg; term = E.do_ap (size + 1) f1 arg} in
    let nf2 = D.Normal {tp = E.do_clos (size + 1) dest2 arg; term = E.do_ap (size + 1) f2 arg} in
    check_nf arg_env (size + 1) nf1 nf2
  (* Pairs *)
  | D.Normal {tp = D.Sg (fst1, snd1); term = p1},
    D.Normal {tp = D.Sg (fst2, snd2); term = p2} ->
    let p11, p21 = E.do_fst p1, E.do_fst p2 in
    let snd1, snd2 = E.do_clos size snd1 p11, E.do_clos size snd2 p21 in
    let p12, p22 = E.do_snd size p1, E.do_snd size p2 in
    check_nf env size (D.Normal {tp = fst1; term = p11}) (D.Normal {tp = fst2; term = p21})
    && check_nf env size (D.Normal {tp = snd1; term = p12}) (D.Normal {tp = snd2; term = p22})
  (* Unit *)
  | D.Normal {tp = D.Unit; term = _},
    D.Normal {tp = D.Unit; term = _} -> true
  (* Numbers *)
  | D.Normal {tp = D.Nat; term = D.Zero},
    D.Normal {tp = D.Nat; term = D.Zero} -> true
  | D.Normal {tp = D.Nat; term = D.Suc nf1},
    D.Normal {tp = D.Nat; term = D.Suc nf2} ->
    check_nf env size (D.Normal {tp = D.Nat; term = nf1}) (D.Normal {tp = D.Nat; term = nf2})
  (* Booleans *)
  | D.Normal {tp = D.Bool; term = D.True},
    D.Normal {tp = D.Bool; term = D.True} -> true
  | D.Normal {tp = D.Bool; term = D.False},
    D.Normal {tp = D.Bool; term = D.False} -> true
  (* Id *)
  | D.Normal {tp = D.Id (tp, _, _); term = D.Refl term1},
    D.Normal {tp = D.Id (_, _, _); term = D.Refl term2} ->
    check_nf env size (D.Normal {tp; term = term1}) (D.Normal {tp; term = term2})
  (* Bridge *)
  | D.Normal {tp = D.Bridge (dest1, _); term = p1},
    D.Normal {tp = D.Bridge (dest2, _); term = p2} ->
    let (arg, arg_env) = mk_bvar env size in
    let nf1 = D.Normal {tp = E.do_bclos (size + 1) dest1 arg; term = E.do_bapp (size + 1) p1 arg} in
    let nf2 = D.Normal {tp = E.do_bclos (size + 1) dest2 arg; term = E.do_bapp (size + 1) p2 arg} in
    check_nf arg_env (size + 1) nf1 nf2
  (* Gel *)
  | D.Normal {tp = D.Gel (_, endtps1, rel1); term = D.Engel (_, ts1, t1)},
    D.Normal {tp = D.Gel (_, endtps2, rel2); term = D.Engel (_, ts2, t2)} ->
    let nfs1 = List.map2 (fun tp term -> D.Normal {tp; term}) endtps1 ts1 in
    let nfs2 = List.map2 (fun tp term -> D.Normal {tp; term}) endtps2 ts2 in
    List.for_all2 (fun nf1 nf2 -> check_nf env size nf1 nf2) nfs1 nfs2 &&
    let applied_rel1 = E.do_closN size rel1 ts1 in
    let applied_rel2 = E.do_closN size rel2 ts2 in
    check_nf env size (D.Normal {tp = applied_rel1; term = t1}) (D.Normal {tp = applied_rel2; term = t2})
  (* Types *)
  | D.Normal {tp = D.Uni _; term = t1}, D.Normal {tp = D.Uni _; term = t2} ->
    check_tp ~subtype:false env size t1 t2
  | D.Normal {tp = _; term = term1}, D.Normal {tp = _; term = term2} ->
    check_quasi_ne env size term1 term2

and check_quasi_ne env size term1 term2 =
  match term1, term2 with
  (* Extent term on the left *)
  | D.Neutral {term = (D.Ext e1, s1); tp = tp1}, _ ->
    begin
      match reduce_extent env size (e1, s1) with
      | Some term1 ->
        check_nf env size (D.Normal {tp = tp1; term = term1}) (D.Normal {tp = tp1; term = term2})
      | None ->
        begin
          match term2 with
          | D.Neutral {term = (D.Ext e2, s2); tp = tp2} ->
            begin
              match reduce_extent env size (e2, s2) with
              | Some term2 ->
                check_nf env size (D.Normal {tp = tp2; term = term1}) (D.Normal {tp = tp2; term = term2})
              | None -> check_ne env size (D.Ext e1, s1) (D.Ext e2, s2)
            end
          | _ -> false
        end
    end
  (* Extent term on the right *)
  | _, D.Neutral {term = (D.Ext e2, s2); tp = tp2} ->
    begin
      match reduce_extent env size (e2, s2) with
      | Some term2 ->
        check_nf env size (D.Normal {tp = tp2; term = term1}) (D.Normal {tp = tp2; term = term2})
      | None ->
        begin
          match term1 with
          | D.Neutral {term = (D.Ext e1, s1); tp = _} ->
            check_ne env size (D.Ext e1, s1) (D.Ext e2, s2)
          | _ -> false
        end
    end
  | D.Neutral {term = ne1; _}, D.Neutral {term = ne2; _} ->
    check_ne env size ne1 ne2
  | _ -> false

and check_ne env size (h1, s1) (h2, s2) =
  match s1, s2 with
  | [], [] ->
    begin
      match h1, h2 with
      | Var i1, Var i2 -> i1 = i2
      | Ext e1, Ext e2 -> check_extent_head env size e1 e2
      | _ -> false
    end
  | D.Ap arg1 :: s1, D.Ap arg2 :: s2 ->
    check_nf env size arg1 arg2 &&
    check_ne env size (h1, s1) (h2, s2)
  | D.NRec (tp1, zero1, suc1) :: s1, D.NRec (tp2, zero2, suc2) :: s2 ->
    let (nat_arg, nat_env) = mk_var D.Nat env size in
    let applied_tp1 = E.do_clos (size + 1) tp1 nat_arg in
    let applied_tp2 = E.do_clos (size + 1) tp2 nat_arg in
    check_tp ~subtype:false nat_env (size + 1) applied_tp1 applied_tp2 &&
    let zero_tp = E.do_clos size tp1 D.Zero in
    check_nf env size (D.Normal {tp = zero_tp; term = zero1}) (D.Normal {tp = zero_tp; term = zero2}) &&
    let (suc_arg, suc_env) = mk_var applied_tp1 nat_env (size + 1) in
    let applied_suc_tp = E.do_clos (size + 2) tp1 (D.Suc nat_arg) in
    let applied_suc1 = E.do_clos2 (size + 2) suc1 nat_arg suc_arg in
    let applied_suc2 = E.do_clos2 (size + 2) suc2 nat_arg suc_arg in
    check_nf suc_env (size + 2)
      (D.Normal {tp = applied_suc_tp; term = applied_suc1})
      (D.Normal {tp = applied_suc_tp; term = applied_suc2}) &&
    check_ne env size (h1, s1) (h2, s2)
  | D.If (mot1, tt1, ff1) :: s1, D.If (mot2, tt2, ff2) :: s2 ->
    let (bool_arg, bool_env) = mk_var D.Bool env size in
    let applied_mot1 = E.do_clos (size + 1) mot1 bool_arg in
    let applied_mot2 = E.do_clos (size + 1) mot2 bool_arg in
    check_tp ~subtype:false bool_env (size + 1) applied_mot1 applied_mot2 &&
    let tt_tp = E.do_clos size mot1 D.True in
    check_nf env size (D.Normal {tp = tt_tp; term = tt1}) (D.Normal {tp = tt_tp; term = tt2}) &&
    let ff_tp = E.do_clos size mot1 D.False in
    check_nf env size (D.Normal {tp = ff_tp; term = ff1}) (D.Normal {tp = ff_tp; term = ff2}) &&
    check_ne env size (h1, s1) (h2, s2)
  | D.Fst :: s1, D.Fst :: s2  -> check_ne env size (h1, s1) (h2, s2)
  | D.Snd :: s1, D.Snd :: s2 -> check_ne env size (h1, s1) (h2, s2)
  | D.BApp i1 :: s1, D.BApp i2 :: s2 ->
    i1 = i2 &&
    check_ne env size (h1, s1) (h2, s2)
  | D.J (mot1, refl1, tp1, left1, right1) :: s1,
    D.J (mot2, refl2, tp2, left2, right2) :: s2 ->
    check_tp ~subtype:false env size tp1 tp2 &&
    check_nf env size (D.Normal {tp = tp1; term = left1}) (D.Normal {tp = tp2; term = left2}) &&
    check_nf env size (D.Normal {tp = tp1; term = right1}) (D.Normal {tp = tp2; term = right2}) &&
    let (mot_arg1, mot_env1) = mk_var tp1 env size in
    let (mot_arg2, mot_env2) = mk_var tp1 mot_env1 (size + 1) in
    let (mot_arg3, mot_env3) = mk_var (D.Id (tp1, left1, right1)) mot_env2 (size + 2) in
    check_tp ~subtype:false mot_env3 (size + 3)
      (E.do_clos3 (size + 3) mot1 mot_arg1 mot_arg2 mot_arg3)
      (E.do_clos3 (size + 3) mot2 mot_arg1 mot_arg2 mot_arg3) &&
    let (refl_arg, refl_env) = mk_var tp1 env size in
    check_nf refl_env (size + 1)
      (D.Normal
         {term = E.do_clos (size + 1) refl1 refl_arg;
          tp = E.do_clos3 (size + 1) mot1 refl_arg refl_arg (D.Refl refl_arg)})
      (D.Normal
         {term = E.do_clos (size + 1) refl2 refl_arg;
          tp = E.do_clos3 (size + 1) mot2 refl_arg refl_arg (D.Refl refl_arg)}) &&
    check_ne env size (h1, s1) (h2, s2)
  | D.Ungel (ends1, rel1, mot1, i1, _, case1) :: s1,
    D.Ungel (_, _, mot2, i2, _, case2) :: s2 ->
    let width = List.length ends1 in
    let sem_env = env_to_sem_env env in
    let end_tps = List.map (function (D.Normal {tp; _}) -> tp) ends1 in
    let end_tms = List.map (function (D.Normal {term; _}) -> term) ends1 in
    let (end_args, _) = mk_vars end_tps env size in
    let applied_rel = E.do_closN size rel1 end_args in
    let mot_inner_env =
      D.Term applied_rel ::
      List.rev_append (List.map (fun t -> D.Term t) end_tps) sem_env in
    let mot_inner_tp =
      Syn.Gel (Syn.BVar 0, List.init width (fun o -> Syn.Var (o + 2)), Syn.Var (width + 1)) in
    let (mot_arg, mot_env) =
      mk_var (D.Bridge (D.Clos {term = mot_inner_tp; env = mot_inner_env}, end_tms)) env size in
    check_tp ~subtype:false mot_env (size + 1)
      (E.do_clos (size + 1) mot1 mot_arg)
      (E.do_clos (size + 1) mot2 mot_arg) &&
    let applied_rel = E.do_closN size rel1 end_tms in
    let (wit_arg, wit_env) = mk_var applied_rel env size in
    let engel_inner_env =
      D.Term wit_arg ::
      List.rev_append (List.map (fun t -> D.Term t) end_tms) sem_env in
    let engel_inner_tm =
      Syn.Engel (Syn.BVar 0, List.init width (fun o -> Syn.Var (o + 2)), Syn.Var 1) in
    let gel_term = D.BLam (D.Clos {term = engel_inner_tm; env = engel_inner_env}) in
    check_nf wit_env (size + 1)
      (D.Normal
         {term = E.do_clos (size + 1) case1 wit_arg;
          tp = E.do_clos (size + 1) mot1 gel_term})
      (D.Normal
         {term = E.do_clos (size + 1) case2 wit_arg;
          tp = E.do_clos (size + 1) mot2 gel_term}) &&
    let ne1' = D.instantiate_ne size i1 (h1, s1) in
    let ne2' = D.instantiate_ne size i2 (h2, s2) in
    check_ne (BVar size :: env) (size + 1) ne1' ne2'
  | _ -> false

and check_extent_head env size
    ({var = i1; dom = dom1; mot = mot1; ctx = ctx1; endcase = endcase1; varcase = varcase1} : D.extent_head)
    ({var = i2; dom = dom2; mot = mot2; ctx = ctx2; endcase = endcase2; varcase = varcase2} : D.extent_head)
  =
  i1 = i2 &&
  let (barg, benv) = mk_bvar env size in
  let applied_dom1 = E.do_bclos (size + 1) dom1 barg in
  let applied_dom2 = E.do_bclos (size + 1) dom2 barg in
  check_tp ~subtype:false benv (size + 1) applied_dom1 applied_dom2 &&
  let (dom_arg, dom_env) = mk_var applied_dom1 benv (size + 1) in
  let applied_mot1 = E.do_bclosclos (size + 2) mot1 barg dom_arg in
  let applied_mot2 = E.do_bclosclos (size + 2) mot2 barg dom_arg in
  check_tp ~subtype:false dom_env (size + 2) applied_mot1 applied_mot2 &&
  let dom_i = E.do_bclos size dom1 (D.BVar i1) in
  check_nf env size (D.Normal {tp = dom_i; term = ctx1}) (D.Normal {tp = dom_i; term = ctx2}) &&
  for_all2i
    (fun o case1 case2 ->
       let case_dom = E.do_bclos size dom1 (D.Const o) in
       let (case_arg, case_env) = mk_var case_dom env size in
       let case_mot = E.do_bclosclos (size + 1) mot1 (D.Const o) case_arg in
       let applied_case1 = E.do_clos (size + 1) case1 case_arg in
       let applied_case2 = E.do_clos (size + 1) case2 case_arg in
       check_nf case_env (size + 1)
         (D.Normal {tp = case_mot; term = applied_case1})
         (D.Normal {tp = case_mot; term = applied_case2}))
    endcase1 endcase2 &&
  let width = List.length endcase1 in
  let endtps = E.do_consts size dom1 width in
  let (end_args, ends_env) = mk_vars endtps env size in
  let (bridge_arg, bridge_env) = mk_var (D.Bridge (dom1, end_args)) ends_env (size + width) in
  let (varcase_barg, varcase_benv) = mk_bvar bridge_env (size + width + 1) in
  let varcase_inst = E.do_bapp (size + width + 2) bridge_arg varcase_barg in
  let varcase_mot = E.do_bclosclos (size + width + 2) mot1 varcase_barg varcase_inst in
  let applied_varcase1 = E.do_clos_extent (size + width + 2) varcase1 end_args bridge_arg varcase_barg in
  let applied_varcase2 = E.do_clos_extent (size + width + 2) varcase2 end_args bridge_arg varcase_barg in
  check_nf varcase_benv (size + width + 2)
    (D.Normal {tp = varcase_mot; term = applied_varcase1})
    (D.Normal {tp = varcase_mot; term = applied_varcase2})

and check_tp ~subtype env size d1 d2 =
  match d1, d2 with
  | D.Unit, D.Unit -> true
  | D.Nat, D.Nat -> true
  | D.Bool, D.Bool -> true
  | D.Id (tp1, left1, right1), D.Id (tp2, left2, right2) ->
    check_tp ~subtype env size tp1 tp2 &&
    check_nf env size (D.Normal {tp = tp1; term = left1}) (D.Normal {tp = tp1; term = left2}) &&
    check_nf env size (D.Normal {tp = tp1; term = right1}) (D.Normal {tp = tp1; term = right2})
  | D.Pi (src, dest), D.Pi (src', dest') ->
    let (arg, arg_env) = mk_var src' env size in
    check_tp ~subtype env size src' src &&
    check_tp ~subtype arg_env (size + 1)
      (E.do_clos (size + 1) dest arg)
      (E.do_clos (size + 1) dest' arg)
  | D.Sg (fst, snd), D.Sg (fst', snd') ->
    let (arg, arg_env) = mk_var fst env size in
    check_tp ~subtype env size fst fst' &&
    check_tp ~subtype arg_env (size + 1)
      (E.do_clos (size + 1) snd arg)
      (E.do_clos (size + 1) snd' arg)
  | D.Bridge (dest, ends), D.Bridge (dest', ends') ->
    let (barg, barg_env) = mk_bvar env size in
    check_tp ~subtype barg_env (size + 1)
      (E.do_bclos (size + 1) dest barg)
      (E.do_bclos (size + 1) dest' barg) &&
    let nfs = List.mapi (fun o term -> D.Normal {tp = E.do_bclos size dest (D.Const o); term}) ends in
    let nfs' = List.mapi (fun o term -> D.Normal {tp = E.do_bclos size dest' (D.Const o); term}) ends' in
    List.for_all2 (check_nf env size) nfs nfs'
  | D.Gel (i, endtps, rel), D.Gel (i', endtps', rel') ->
    i = i' &&
    List.for_all2 (check_tp ~subtype env size) endtps endtps' &&
    let (rel_args, rel_env) = mk_vars endtps env size in
    let rel_size = size + List.length endtps in
    check_tp ~subtype rel_env rel_size
      (E.do_closN rel_size rel rel_args)
      (E.do_closN rel_size rel' rel_args)
  | D.Uni k, D.Uni j -> if subtype then k <= j else k = j
  | _ -> check_quasi_ne env size d1 d2
