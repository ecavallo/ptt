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
  | DVar of D.lvl
  | Var of {level : D.lvl; tp : D.t}
  | Def of D.t
  | TopLevel of D.t
  | Postulate of {level : D.lvl; tp : D.t}
type env = env_entry list

let mk_bvar env size =
  (D.DVar size, DVar size :: env)

let mk_var tp env size =
  (D.Neutral {tp; term = D.root (D.Var size)}, Var {level = size; tp} :: env)

let mk_vars tps env size =
  (List.mapi (fun i tp -> D.Neutral {tp; term = D.root (D.Var (size + i))}) tps,
   List.rev_append
     (List.mapi (fun i tp -> Var {level = size + i; tp}) tps)
     env)

let env_to_sem_env env =
  let go = function
    | DVar i -> D.Dim (D.DVar i)
    | Var {level; tp} -> D.Tm (D.Neutral {tp; term = D.root (D.Var level)})
    | Def term -> D.Tm term
    | TopLevel term -> D.TopLevel term
    | Postulate {level; tp} -> D.TopLevel (D.Neutral {tp; term = D.root (D.Var level)})
  in
  List.map go env

let read_back_level env x =
  let rec go acc = function
    | DVar i :: env -> if i = x then acc else go (acc + 1) env
    | Var {level; _} :: env -> if level = x then acc else go (acc + 1) env
    | Def _ :: env -> go (acc + 1) env
    | TopLevel _ :: env -> go (acc + 1) env
    | Postulate {level; _} :: env -> if level = x then acc else go (acc + 1) env
    | [] -> raise (Quote_failed "read back non-existent variable")
  in
  go 0 env

let read_back_dim env = function
  | D.DVar i -> Syn.DVar (read_back_level env i)
  | D.Const o -> Syn.Const o

exception Cannot_reduce_extent

let rec reduce_extent_head env size ({var = i; dom; ctx; endcase; varcase; _} : D.extent_head) =
  let sem_env = env_to_sem_env env in
  let dom_i = E.do_clos size dom (D.Dim (D.DVar i)) in
  let i' = read_back_level env i in
  let ctx' = read_back_nf env size (D.Normal {tp = dom_i; term = ctx}) in
  begin
    match Syntax.unsubst_bvar i' ctx' with
    | Some extract ->
      let extract_ends =
        List.init (List.length endcase) (fun o -> E.eval extract (D.Dim (D.Const o) :: sem_env) size) in
      let extract_blam =
        D.BLam (D.Clos {term = extract; env = sem_env}) in
      let output_varcase = E.do_clos_extent size varcase extract_ends extract_blam (D.DVar i) in
      output_varcase
    | _ -> raise Cannot_reduce_extent
  end

and reduce_extent env size es =
  let rec go env size (e, s) =
    match s with
    | [] -> reduce_extent_head env size e
    | D.Ap (Normal {term; _}) :: s -> E.do_ap size (go env size (e, s)) term
    | D.NRec (tp, zero, suc) :: s -> E.do_rec size tp zero suc (go env size (e, s))
    | D.ListRec (_, mot, nil, cons) :: s -> E.do_list_rec size mot nil cons (go env size (e, s))
    | D.If (mot, tt, ff) :: s -> E.do_if size mot tt ff (go env size (e, s))
    | D.Case (_, _, mot, inl, inr) :: s -> E.do_case size mot inl inr (go env size (e, s))
    | D.Abort mot :: s -> E.do_abort size mot (go env size (e, s))
    | D.Fst :: s -> E.do_fst (go env size (e, s))
    | D.Snd :: s -> E.do_snd size (go env size (e, s))
    | D.BApp r :: s -> E.do_bapp size (go env size (e, s)) r
    | D.J (mot, refl, _, _, _) :: s -> E.do_j size mot refl (go env size (e, s))
    | D.Ungel (end_tms, _, _, mot, i, case) :: s ->
      let es' = D.instantiate_spine D.instantiate_extent_head size i (e, s) in
      E.do_ungel size end_tms mot (go (DVar size :: env) (size + 1) es') case
    | D.Uncodisc :: s -> E.do_uncodisc (go env size (e, s))
    | D.Unglobe :: s -> E.do_unglobe (go env size (e, s))
    | D.Quasi q :: s ->
      begin
        match q with 
        | D.PiDom -> E.do_pi_dom (go env size (e,s))
        | D.PiCod a -> E.do_pi_cod size (go env size (e,s)) a
        | D.SgDom -> E.do_sg_dom (go env size (e,s))
        | D.SgCod a -> E.do_sg_cod size (go env size (e,s)) a
        | D.ListTp -> E.do_list_tp (go env size (e,s))
        | D.CoprodLeft -> E.do_coprod_left (go env size (e,s))
        | D.CoprodRight -> E.do_coprod_right (go env size (e,s))
        | D.IdLeft -> E.do_id_left (go env size (e,s))
        | D.IdRight -> E.do_id_right (go env size (e,s))
        | D.IdTp -> E.do_id_tp (go env size (e,s))
        | D.BridgeCod r -> E.do_bridge_cod size (go env size (e,s)) r
        | D.BridgeEndpoint (ne, o) -> E.do_bridge_endpoint size (go env size (e,s)) ne o
        | D.GelRel ts -> E.do_gel_rel size (go env size (e,s)) ts
        | D.GelBridge ts -> E.do_gel_bridge size (go env size (e,s)) ts
        | D.GlobalTp -> E.do_global_tp (go env size (e,s))
        | D.CodiscTp -> E.do_codisc_tp (go env size (e,s))
      end
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
        {tp = E.do_clos (size + 1) dest (D.Tm arg);
         term = E.do_ap (size + 1) f arg} in
    Syn.Lam (read_back_nf arg_env (size + 1) nf)
  (* Pairs *)
  | D.Normal {tp = D.Sg (fst, snd); term = p} ->
    let fst' = E.do_fst p in
    let snd = E.do_clos size snd (D.Tm fst') in
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
  (* Lists *)
  | D.Normal {tp = D.List _; term = D.Nil} -> Syn.Nil
  | D.Normal {tp = D.List tp; term = D.Cons (a, t)} ->
    Syn.Cons
      (read_back_nf env size (D.Normal {tp; term = a}),
       read_back_nf env size (D.Normal {tp = D.List tp; term = t}))
  (* Booleans *)
  | D.Normal {tp = D.Bool; term = D.True} -> Syn.True
  | D.Normal {tp = D.Bool; term = D.False} -> Syn.False
  (* Coproducts *)
  | D.Normal {tp = D.Coprod (tp, _); term = D.Inl term} ->
    Syn.Inl (read_back_nf env size (D.Normal {tp; term}))
  | D.Normal {tp = D.Coprod (_, tp); term = D.Inr term} ->
    Syn.Inr (read_back_nf env size (D.Normal {tp; term}))
  (* Bridge *)
  | D.Normal {tp = D.Bridge (dest, _); term} ->
    let (arg, arg_env) = mk_bvar env size in
    let nf = D.Normal
        {tp = E.do_clos (size + 1) dest (D.Dim arg);
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
      (i',
       List.map2 (fun tp term -> read_back_nf env size (D.Normal {tp; term})) endtps ts,
       read_back_nf env size (D.Normal {tp = applied_rel; term = t}))
  (* Codisc *)
  | D.Normal {tp = D.Codisc tp; term = t} ->
    let t' = E.do_uncodisc t in
    Syn.Encodisc (read_back_nf env size (D.Normal {tp; term = t'}))
  (* Global *)
  | D.Normal {tp = D.Global tp; term = t} ->
    let t' = E.do_unglobe t in
    Syn.Englobe (read_back_nf env size (D.Normal {tp; term = t'}))
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
  | D.List t -> Syn.List (read_back_tp env size t)
  | D.Bool -> Syn.Bool
  | D.Coprod (t1, t2) -> Syn.Coprod (read_back_tp env size t1, read_back_tp env size t2)
  | D.Void -> Syn.Void
  | D.Pi (src, dest) ->
    let (arg, arg_env) = mk_var src env size in
    Syn.Pi
      (read_back_tp env size src,
       read_back_tp arg_env (size + 1) (E.do_clos (size + 1) dest (D.Tm arg)))
  | D.Sg (fst, snd) ->
    let (arg, arg_env) = mk_var fst env size in
    Syn.Sg
      (read_back_tp env size fst,
       read_back_tp arg_env (size + 1) (E.do_clos (size + 1) snd (D.Tm arg)))
  | D.Bridge (dest, ends) ->
    let width = List.length ends in
    let (arg, arg_env) = mk_bvar env size in
    Syn.Bridge
      (read_back_tp arg_env (size + 1) (E.do_clos (size + 1) dest (D.Dim arg)),
       List.map2
         (fun tp -> Option.map (fun term -> read_back_nf env size (D.Normal {tp; term})))
         (E.do_consts size dest width)
         ends)
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
      (Syn.DVar i',
       List.map (read_back_tp env size) endtps,
       read_back_tp rel_env rel_size (E.do_closN rel_size rel rel_args))
  | D.Codisc tp -> Syn.Codisc (read_back_tp env size tp)
  | D.Global tp -> Syn.Global (read_back_tp env size tp)
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
    let applied_tp = E.do_clos (size + 1) tp (D.Tm nat_arg) in
    let tp' = read_back_tp nat_env (size + 1) applied_tp in
    let zero_tp = E.do_clos size tp (D.Tm D.Zero) in
    let zero' = read_back_nf env size (D.Normal {tp = zero_tp; term = zero}) in
    let (suc_arg, suc_env) = mk_var applied_tp nat_env (size + 1) in
    let applied_suc_tp = E.do_clos (size + 2) tp (D.Tm (D.Suc nat_arg)) in
    let applied_suc = E.do_clos2 (size + 2) suc (D.Tm nat_arg) (D.Tm suc_arg) in
    let suc' = read_back_nf suc_env (size + 2) (D.Normal {tp = applied_suc_tp; term = applied_suc}) in
    Syn.NRec (tp', zero', suc', read_back_ne env size (h, s))
  | D.ListRec (tp, mot, nil, cons) :: s ->
    let (list_arg, list_env) = mk_var (D.List tp) env size in
    let applied_mot = E.do_clos (size + 1) mot (D.Tm list_arg) in
    let mot' = read_back_tp list_env (size + 1) applied_mot in
    let nil_mot = E.do_clos size mot (D.Tm D.Nil) in
    let nil' = read_back_nf env size (D.Normal {tp = nil_mot; term = nil}) in
    let (cons_arg1, cons_env1) = mk_var tp env size in
    let (cons_arg2, cons_env2) = mk_var (D.List tp) cons_env1 (size + 1) in
    let rec_mot = E.do_clos (size + 2) mot (D.Tm cons_arg2) in
    let (cons_arg3, cons_env3) = mk_var rec_mot cons_env2 (size + 2) in
    let cons_mot = E.do_clos (size + 3) mot (D.Tm (D.Cons (cons_arg1, cons_arg2))) in
    let applied_cons = E.do_clos3 (size + 3) cons cons_arg1 cons_arg2 cons_arg3 in
    let cons' = read_back_nf cons_env3 (size + 3) (D.Normal {tp = cons_mot; term = applied_cons}) in
    Syn.ListRec (mot', nil', cons', read_back_ne env size (h, s))
  | D.If (mot, tt, ff) :: s ->
    let (bool_arg, bool_env) = mk_var D.Bool env size in
    let applied_mot = E.do_clos (size + 1) mot (D.Tm bool_arg) in
    let mot' = read_back_tp bool_env (size + 1) applied_mot in
    let tt_tp = E.do_clos size mot (D.Tm D.True) in
    let tt' = read_back_nf env size (D.Normal {tp = tt_tp; term = tt}) in
    let ff_tp = E.do_clos size mot (D.Tm D.False) in
    let ff' = read_back_nf env size (D.Normal {tp = ff_tp; term = ff}) in
    Syn.If (mot', tt', ff', read_back_ne env size (h, s))
  | D.Case (left, right, mot, inl, inr) :: s ->
    let (mot_arg, mot_env) = mk_var (D.Coprod (left, right)) env size in
    let applied_mot = E.do_clos (size + 1) mot (D.Tm mot_arg) in
    let mot' = read_back_tp mot_env (size + 1) applied_mot in
    let (inl_arg, inl_env) = mk_var left env size in
    let inl_mot = E.do_clos (size + 1) mot (D.Tm (D.Inl inl_arg)) in
    let applied_inl = E.do_clos (size + 1) inl (D.Tm inl_arg) in
    let inl' = read_back_nf inl_env (size + 1) (D.Normal {tp = inl_mot; term = applied_inl}) in
    let (inr_arg, inr_env) = mk_var right env size in
    let inr_mot = E.do_clos (size + 1) mot (D.Tm (D.Inr inr_arg)) in
    let applied_inr = E.do_clos (size + 1) inr (D.Tm inr_arg) in
    let inr' = read_back_nf inr_env (size + 1) (D.Normal {tp = inr_mot; term = applied_inr}) in
    Syn.Case (mot', inl', inr', read_back_ne env size (h, s))
  | D.Abort mot :: s ->
    let (mot_arg, mot_env) = mk_var D.Void env size in
    let applied_mot = E.do_clos (size + 1) mot (D.Tm mot_arg) in
    let mot' = read_back_tp mot_env (size + 1) applied_mot in
    Syn.Abort (mot', read_back_ne env size (h, s))
  | D.Fst :: s -> Syn.Fst (read_back_ne env size (h, s))
  | D.Snd :: s -> Syn.Snd (read_back_ne env size (h, s))
  | D.BApp r :: s ->
    Syn.BApp (read_back_ne env size (h, s), read_back_dim env r)
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
           {term = E.do_clos (size + 1) refl (D.Tm refl_arg);
            tp = E.do_clos3 (size + 1) mot refl_arg refl_arg (D.Refl refl_arg)}) in
    Syn.J (mot_syn, refl_syn, read_back_ne env size (h, s))
  | D.Ungel (end_tms, rel, bri, mot, i, case) :: s ->
    let (mot_arg, mot_env) = mk_var bri env size in
    let mot' = read_back_tp mot_env (size + 1) (E.do_clos (size + 1) mot (D.Tm mot_arg)) in
    let (wit_arg, wit_env) = mk_var rel env size in
    let gel_term =
      D.BLam (D.Pseudo {var = size + 1; term = D.Engel (size + 1, end_tms, wit_arg); ends = end_tms}) in
    let case' = read_back_nf
        wit_env
        (size + 1)
        (D.Normal
           {term = E.do_clos (size + 1) case (D.Tm wit_arg);
            tp = E.do_clos (size + 1) mot (D.Tm gel_term)}) in
    let ne' = D.instantiate_ne size i (h, s) in
    Syn.Ungel (List.length end_tms, mot', read_back_ne (DVar size :: env) (size + 1) ne', case')
  | D.Uncodisc :: s -> Syn.Uncodisc (read_back_ne env size (h, s))
  | D.Unglobe :: s -> Syn.Unglobe (read_back_ne env size (h, s))
  | D.Quasi _ :: _ ->
    failwith "Invariant: this can never happen"


and read_back_extent_head env size ({var = i; dom; mot; ctx; endcase; varcase} : D.extent_head) =
  let i' = read_back_level env i in
  let (barg, benv) = mk_bvar env size in
  let applied_dom = E.do_clos (size + 1) dom (D.Dim barg) in
  let dom' = read_back_tp benv (size + 1) applied_dom in
  let (dom_arg, dom_env) = mk_var applied_dom benv (size + 1) in
  let applied_mot = E.do_clos2 (size + 2) mot (D.Dim barg) (D.Tm dom_arg) in
  let mot' = read_back_tp dom_env (size + 2) applied_mot in
  let dom_i = E.do_clos size dom (D.Dim (D.DVar i)) in
  let ctx' = read_back_nf env size (D.Normal {tp = dom_i; term = ctx}) in
  let endcase' =
    List.mapi
      (fun o case ->
         let case_dom = E.do_clos size dom (D.Dim (D.Const o)) in
         let (case_arg, case_env) = mk_var case_dom env size in
         let case_mot = E.do_clos2 (size + 1) mot (D.Dim (D.Const o)) (D.Tm case_arg) in
         let applied_case = E.do_clos (size + 1) case (D.Tm case_arg) in
         read_back_nf case_env (size + 1) (D.Normal {tp = case_mot; term = applied_case}))
      endcase in
  let width = List.length endcase in
  let endtps = E.do_consts size dom width in
  let (end_args, ends_env) = mk_vars endtps env size in
  let (bridge_arg, bridge_env) =
    mk_var (D.Bridge (dom, List.map Option.some end_args)) ends_env (size + width) in
  let (varcase_barg, varcase_benv) = mk_bvar bridge_env (size + width + 1) in
  let varcase_inst = E.do_bapp (size + width + 2) bridge_arg varcase_barg in
  let varcase_mot = E.do_clos2 (size + width + 2) mot (D.Dim varcase_barg) (D.Tm varcase_inst) in
  let applied_varcase = E.do_clos_extent (size + width + 2) varcase end_args bridge_arg varcase_barg in
  let varcase' =
    read_back_nf varcase_benv (size + width + 2) (D.Normal {tp = varcase_mot; term = applied_varcase})
  in
  Syn.Extent (Syn.DVar i', dom', mot', ctx', endcase', varcase')

let rec check_nf env size nf1 nf2 =
  match nf1, nf2 with
  (* Functions *)
  | D.Normal {tp = D.Pi (src1, dest1); term = f1},
    D.Normal {tp = D.Pi (_, dest2); term = f2} ->
    let (arg, arg_env) = mk_var src1 env size in
    let nf1 = D.Normal {tp = E.do_clos (size + 1) dest1 (D.Tm arg); term = E.do_ap (size + 1) f1 arg} in
    let nf2 = D.Normal {tp = E.do_clos (size + 1) dest2 (D.Tm arg); term = E.do_ap (size + 1) f2 arg} in
    check_nf arg_env (size + 1) nf1 nf2
  (* Pairs *)
  | D.Normal {tp = D.Sg (fst1, snd1); term = p1},
    D.Normal {tp = D.Sg (fst2, snd2); term = p2} ->
    let p11, p21 = E.do_fst p1, E.do_fst p2 in
    let snd1, snd2 = E.do_clos size snd1 (D.Tm p11), E.do_clos size snd2 (D.Tm p21) in
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
  (* Lists *)
  | D.Normal {tp = D.List _; term = D.Nil},
    D.Normal {tp = D.List _; term = D.Nil} -> true
  | D.Normal {tp = D.List tp; term = D.Cons (a1, t1)},
    D.Normal {tp = D.List _; term = D.Cons (a2, t2)} ->
    check_nf env size (D.Normal {tp; term = a1}) (D.Normal {tp; term = a2}) &&
    check_nf env size (D.Normal {tp = D.List tp; term = t1}) (D.Normal {tp = D.List tp; term = t2})
  (* Booleans *)
  | D.Normal {tp = D.Bool; term = D.True},
    D.Normal {tp = D.Bool; term = D.True} -> true
  | D.Normal {tp = D.Bool; term = D.False},
    D.Normal {tp = D.Bool; term = D.False} -> true
  (* Coproducts *)
  | D.Normal {tp = D.Coprod (tp, _); term = D.Inl term1},
    D.Normal {tp = D.Coprod (_, _); term = D.Inl term2} ->
    check_nf env size (D.Normal {tp; term = term1}) (D.Normal {tp; term = term2})
  | D.Normal {tp = D.Coprod (_, tp); term = D.Inr term1},
    D.Normal {tp = D.Coprod (_, _); term = D.Inr term2} ->
    check_nf env size (D.Normal {tp; term = term1}) (D.Normal {tp; term = term2})
  (* Id *)
  | D.Normal {tp = D.Id (tp, _, _); term = D.Refl term1},
    D.Normal {tp = D.Id (_, _, _); term = D.Refl term2} ->
    check_nf env size (D.Normal {tp; term = term1}) (D.Normal {tp; term = term2})
  (* Bridge *)
  | D.Normal {tp = D.Bridge (dest1, _); term = p1},
    D.Normal {tp = D.Bridge (dest2, _); term = p2} ->
    let (arg, arg_env) = mk_bvar env size in
    let nf1 = D.Normal {tp = E.do_clos (size + 1) dest1 (D.Dim arg); term = E.do_bapp (size + 1) p1 arg} in
    let nf2 = D.Normal {tp = E.do_clos (size + 1) dest2 (D.Dim arg); term = E.do_bapp (size + 1) p2 arg} in
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
  (* Codisc *)
  | D.Normal {tp = D.Codisc tp1; term = t1}, D.Normal {tp = D.Codisc tp2; term = t2} ->
    let t1',t2' = E.do_uncodisc t1, E.do_uncodisc t2 in
    check_nf env size (D.Normal {tp = tp1; term = t1'}) (D.Normal {tp = tp2; term = t2'})
  (* Global *)
  | D.Normal {tp = D.Global tp1; term = t1}, D.Normal {tp = D.Global tp2; term = t2} ->
    let t1',t2' = E.do_unglobe t1, E.do_unglobe t2 in
    check_nf env size (D.Normal {tp = tp1; term = t1'}) (D.Normal {tp = tp2; term = t2'})
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
    let applied_tp1 = E.do_clos (size + 1) tp1 (D.Tm nat_arg) in
    let applied_tp2 = E.do_clos (size + 1) tp2 (D.Tm nat_arg) in
    check_tp ~subtype:false nat_env (size + 1) applied_tp1 applied_tp2 &&
    let zero_tp = E.do_clos size tp1 (D.Tm D.Zero) in
    check_nf env size (D.Normal {tp = zero_tp; term = zero1}) (D.Normal {tp = zero_tp; term = zero2}) &&
    let (suc_arg, suc_env) = mk_var applied_tp1 nat_env (size + 1) in
    let applied_suc_tp = E.do_clos (size + 2) tp1 (D.Tm (D.Suc nat_arg)) in
    let applied_suc1 = E.do_clos2 (size + 2) suc1 (D.Tm nat_arg) (D.Tm suc_arg) in
    let applied_suc2 = E.do_clos2 (size + 2) suc2 (D.Tm nat_arg) (D.Tm suc_arg) in
    check_nf suc_env (size + 2)
      (D.Normal {tp = applied_suc_tp; term = applied_suc1})
      (D.Normal {tp = applied_suc_tp; term = applied_suc2}) &&
    check_ne env size (h1, s1) (h2, s2)
  | D.ListRec (tp, mot1, nil1, cons1) :: s1, D.ListRec (_, mot2, nil2, cons2) :: s2 ->
    let (list_arg, list_env) = mk_var (D.List tp) env size in
    let applied_mot1 = E.do_clos (size + 1) mot1 (D.Tm list_arg) in
    let applied_mot2 = E.do_clos (size + 1) mot2 (D.Tm list_arg) in
    check_tp ~subtype:false list_env (size + 1) applied_mot1 applied_mot2 &&
    let nil_mot = E.do_clos size mot1 (D.Tm D.Nil) in
    check_nf env size (D.Normal {tp = nil_mot; term = nil1}) (D.Normal {tp = nil_mot; term = nil2}) &&
    let (cons_arg1, cons_env1) = mk_var tp env size in
    let (cons_arg2, cons_env2) = mk_var (D.List tp) cons_env1 (size + 1) in
    let rec_mot = E.do_clos (size + 2) mot1 (D.Tm cons_arg2) in
    let (cons_arg3, cons_env3) = mk_var rec_mot cons_env2 (size + 2) in
    let cons_mot = E.do_clos (size + 3) mot1 (D.Tm (D.Cons (cons_arg1, cons_arg2))) in
    let applied_cons1 = E.do_clos3 (size + 3) cons1 cons_arg1 cons_arg2 cons_arg3 in
    let applied_cons2 = E.do_clos3 (size + 3) cons2 cons_arg1 cons_arg2 cons_arg3 in
    check_nf cons_env3 (size + 3)
      (D.Normal {tp = cons_mot; term = applied_cons1})
      (D.Normal {tp = cons_mot; term = applied_cons2}) &&
    check_ne env size (h1, s1) (h2, s2)
  | D.If (mot1, tt1, ff1) :: s1, D.If (mot2, tt2, ff2) :: s2 ->
    let (bool_arg, bool_env) = mk_var D.Bool env size in
    let applied_mot1 = E.do_clos (size + 1) mot1 (D.Tm bool_arg) in
    let applied_mot2 = E.do_clos (size + 1) mot2 (D.Tm bool_arg) in
    check_tp ~subtype:false bool_env (size + 1) applied_mot1 applied_mot2 &&
    let tt_tp = E.do_clos size mot1 (D.Tm D.True) in
    check_nf env size (D.Normal {tp = tt_tp; term = tt1}) (D.Normal {tp = tt_tp; term = tt2}) &&
    let ff_tp = E.do_clos size mot1 (D.Tm D.False) in
    check_nf env size (D.Normal {tp = ff_tp; term = ff1}) (D.Normal {tp = ff_tp; term = ff2}) &&
    check_ne env size (h1, s1) (h2, s2)
  | D.Case (left, right, mot1, inl1, inr1) :: s1,
    D.Case (_, _, mot2, inl2, inr2) :: s2 ->
    let (mot_arg, mot_env) = mk_var (D.Coprod (left, right)) env size in
    let applied_mot1 = E.do_clos (size + 1) mot1 (D.Tm mot_arg) in
    let applied_mot2 = E.do_clos (size + 1) mot2 (D.Tm mot_arg) in
    check_tp ~subtype:false mot_env (size + 1) applied_mot1 applied_mot2 &&
    let (inl_arg, inl_env) = mk_var left env size in
    let inl_mot = E.do_clos (size + 1) mot1 (D.Tm (D.Inl inl_arg)) in
    let applied_inl1 = E.do_clos (size + 1) inl1 (D.Tm inl_arg) in
    let applied_inl2 = E.do_clos (size + 1) inl2 (D.Tm inl_arg) in
    check_nf inl_env (size + 1)
      (D.Normal {tp = inl_mot; term = applied_inl1})
      (D.Normal {tp = inl_mot; term = applied_inl2}) &&
    let (inr_arg, inr_env) = mk_var right env size in
    let inr_mot = E.do_clos (size + 1) mot1 (D.Tm (D.Inr inr_arg)) in
    let applied_inr1 = E.do_clos (size + 1) inr1 (D.Tm inr_arg) in
    let applied_inr2 = E.do_clos (size + 1) inr2 (D.Tm inr_arg) in
    check_nf inr_env (size + 1)
      (D.Normal {tp = inr_mot; term = applied_inr1})
      (D.Normal {tp = inr_mot; term = applied_inr2}) &&
    check_ne env size (h1, s1) (h2, s2)
  | D.Abort mot1 :: s1, D.Abort mot2 :: s2 ->
    let (mot_arg, mot_env) = mk_var D.Void env size in
    let applied_mot1 = E.do_clos (size + 1) mot1 (D.Tm mot_arg) in
    let applied_mot2 = E.do_clos (size + 1) mot2 (D.Tm mot_arg) in
    check_tp ~subtype:false mot_env (size + 1) applied_mot1 applied_mot2 &&
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
         {term = E.do_clos (size + 1) refl1 (D.Tm refl_arg);
          tp = E.do_clos3 (size + 1) mot1 refl_arg refl_arg (D.Refl refl_arg)})
      (D.Normal
         {term = E.do_clos (size + 1) refl2 (D.Tm refl_arg);
          tp = E.do_clos3 (size + 1) mot2 refl_arg refl_arg (D.Refl refl_arg)}) &&
    check_ne env size (h1, s1) (h2, s2)
  | D.Ungel (end_tms1, rel1, bri1, mot1, i1, case1) :: s1,
    D.Ungel (_, _, _, mot2, i2, case2) :: s2 ->
    let (mot_arg, mot_env) = mk_var bri1 env size in
    check_tp ~subtype:false mot_env (size + 1)
      (E.do_clos (size + 1) mot1 (D.Tm mot_arg))
      (E.do_clos (size + 1) mot2 (D.Tm mot_arg)) &&
    let (wit_arg, wit_env) = mk_var rel1 env size in
    let gel_term =
      D.BLam (D.Pseudo {var = size + 1; term = D.Engel (size + 1, end_tms1, wit_arg); ends = end_tms1}) in
    check_nf wit_env (size + 1)
      (D.Normal
         {term = E.do_clos (size + 1) case1 (D.Tm wit_arg);
          tp = E.do_clos (size + 1) mot1 (D.Tm gel_term)})
      (D.Normal
         {term = E.do_clos (size + 1) case2 (D.Tm wit_arg);
          tp = E.do_clos (size + 1) mot2 (D.Tm gel_term)}) &&
    let ne1' = D.instantiate_ne size i1 (h1, s1) in
    let ne2' = D.instantiate_ne size i2 (h2, s2) in
    check_ne (DVar size :: env) (size + 1) ne1' ne2'
  | D.Uncodisc :: s1, D.Uncodisc :: s2 -> check_ne env size (h1, s1) (h2, s2)
  | D.Unglobe :: s1, D.Unglobe :: s2 -> check_ne env size (h1, s1) (h2, s2)
  | _ -> false

and check_extent_head env size
    ({var = i1; dom = dom1; mot = mot1; ctx = ctx1; endcase = endcase1; varcase = varcase1} : D.extent_head)
    ({var = i2; dom = dom2; mot = mot2; ctx = ctx2; endcase = endcase2; varcase = varcase2} : D.extent_head)
  =
  i1 = i2 &&
  let (barg, benv) = mk_bvar env size in
  let applied_dom1 = E.do_clos (size + 1) dom1 (D.Dim barg) in
  let applied_dom2 = E.do_clos (size + 1) dom2 (D.Dim barg) in
  check_tp ~subtype:false benv (size + 1) applied_dom1 applied_dom2 &&
  let (dom_arg, dom_env) = mk_var applied_dom1 benv (size + 1) in
  let applied_mot1 = E.do_clos2 (size + 2) mot1 (D.Dim barg) (D.Tm dom_arg) in
  let applied_mot2 = E.do_clos2 (size + 2) mot2 (D.Dim barg) (D.Tm dom_arg) in
  check_tp ~subtype:false dom_env (size + 2) applied_mot1 applied_mot2 &&
  let dom_i = E.do_clos size dom1 (D.Dim (D.DVar i1)) in
  check_nf env size (D.Normal {tp = dom_i; term = ctx1}) (D.Normal {tp = dom_i; term = ctx2}) &&
  for_all2i
    (fun o case1 case2 ->
       let case_dom = E.do_clos size dom1 (D.Dim (D.Const o)) in
       let (case_arg, case_env) = mk_var case_dom env size in
       let case_mot = E.do_clos2 (size + 1) mot1 (D.Dim (D.Const o)) (D.Tm case_arg) in
       let applied_case1 = E.do_clos (size + 1) case1 (D.Tm case_arg) in
       let applied_case2 = E.do_clos (size + 1) case2 (D.Tm case_arg) in
       check_nf case_env (size + 1)
         (D.Normal {tp = case_mot; term = applied_case1})
         (D.Normal {tp = case_mot; term = applied_case2}))
    endcase1 endcase2 &&
  let width = List.length endcase1 in
  let endtps = E.do_consts size dom1 width in
  let (end_args, ends_env) = mk_vars endtps env size in
  let (bridge_arg, bridge_env) =
    mk_var (D.Bridge (dom1, List.map Option.some end_args)) ends_env (size + width) in
  let (varcase_barg, varcase_benv) = mk_bvar bridge_env (size + width + 1) in
  let varcase_inst = E.do_bapp (size + width + 2) bridge_arg varcase_barg in
  let varcase_mot = E.do_clos2 (size + width + 2) mot1 (D.Dim varcase_barg) (D.Tm varcase_inst) in
  let applied_varcase1 = E.do_clos_extent (size + width + 2) varcase1 end_args bridge_arg varcase_barg in
  let applied_varcase2 = E.do_clos_extent (size + width + 2) varcase2 end_args bridge_arg varcase_barg in
  check_nf varcase_benv (size + width + 2)
    (D.Normal {tp = varcase_mot; term = applied_varcase1})
    (D.Normal {tp = varcase_mot; term = applied_varcase2})

and check_tp ~subtype env size d1 d2 =
  match d1, d2 with
  | D.Unit, D.Unit -> true
  | D.Nat, D.Nat -> true
  | D.List t, D.List t' -> check_tp ~subtype env size t t'
  | D.Bool, D.Bool -> true
  | D.Coprod (a, b), D.Coprod (a', b') ->
    check_tp ~subtype env size a a' &&
    check_tp ~subtype env size b b'
  | D.Void, D.Void -> true
  | D.Id (tp1, left1, right1), D.Id (tp2, left2, right2) ->
    check_tp ~subtype env size tp1 tp2 &&
    check_nf env size (D.Normal {tp = tp1; term = left1}) (D.Normal {tp = tp1; term = left2}) &&
    check_nf env size (D.Normal {tp = tp1; term = right1}) (D.Normal {tp = tp1; term = right2})
  | D.Pi (src, dest), D.Pi (src', dest') ->
    let (arg, arg_env) = mk_var src' env size in
    check_tp ~subtype env size src' src &&
    check_tp ~subtype arg_env (size + 1)
      (E.do_clos (size + 1) dest (D.Tm arg))
      (E.do_clos (size + 1) dest' (D.Tm arg))
  | D.Sg (fst, snd), D.Sg (fst', snd') ->
    let (arg, arg_env) = mk_var fst env size in
    check_tp ~subtype env size fst fst' &&
    check_tp ~subtype arg_env (size + 1)
      (E.do_clos (size + 1) snd (D.Tm arg))
      (E.do_clos (size + 1) snd' (D.Tm arg))
  | D.Bridge (dest, ends), D.Bridge (dest', ends') ->
    let width = List.length ends in
    let (barg, barg_env) = mk_bvar env size in
    check_tp ~subtype barg_env (size + 1)
      (E.do_clos (size + 1) dest (D.Dim barg))
      (E.do_clos (size + 1) dest' (D.Dim barg)) &&
    let nfs = List.map2
        (fun tp -> Option.map (fun term -> D.Normal {tp; term}))
        (E.do_consts size dest width) ends in
    let nfs' = List.map2
        (fun tp -> Option.map (fun term -> D.Normal {tp; term}))
        (E.do_consts size dest width) ends' in
    let go nf nf' =
      match nf, nf' with
      | Some nf, Some nf' -> check_nf env size nf nf'
      | Some _, None -> subtype
      | None, Some _ -> false
      | None, None -> true
    in
    List.for_all2 go nfs nfs'
  | D.Gel (i, endtps, rel), D.Gel (i', endtps', rel') ->
    i = i' &&
    List.for_all2 (check_tp ~subtype env size) endtps endtps' &&
    let (rel_args, rel_env) = mk_vars endtps env size in
    let rel_size = size + List.length endtps in
    check_tp ~subtype rel_env rel_size
      (E.do_closN rel_size rel rel_args)
      (E.do_closN rel_size rel' rel_args)
  | D.Codisc tp, D.Codisc tp' -> check_tp ~subtype env size tp tp'
  | D.Global tp, D.Global tp' -> check_tp ~subtype env size tp tp'
  | D.Uni k, D.Uni j -> if subtype then k <= j else k = j
  | _ -> check_quasi_ne env size d1 d2
