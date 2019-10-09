module Syn = Syntax
module D = Domain
module E = Eval

exception Quote_failed of string

exception Removed

type env_entry =
  | BVar of int
  | Var of {level : int; tp : Domain.t}
  | Def of {term : Domain.t; tp : Domain.t}
[@@deriving show]
type env = env_entry list * int
[@@deriving show]

let get_range (_, range) = range

let mk_bvar (entries, range) =
  (D.BVar range, (BVar range :: entries, range + 1))

let mk_var tp (entries, range) =
  (D.Neutral {tp; term = Root range}, (Var {level = range; tp} :: entries, range + 1))

let add_def ~term ~tp (entries, range) =
  (Def {term; tp} :: entries, range)

let add_bvar i (entries, range) =
  (BVar i :: entries, range)

let expose root_inst i stack (entries, range) =
  (range, D.instantiate_stack root_inst range i stack, (BVar range :: entries, range + 1))

let env_to_sem_env (entries, range) =
  let go = function
    | BVar i -> D.BDim (D.BVar i)
    | Var {level; tp} -> D.Term (D.Neutral {tp; term = D.Root level})
    | Def {term; _} -> D.Term term
  in
  (List.map go entries, range)

let restrict_env r (entries, range) =
  let rec go i = function
  | [] -> []
  | BVar j :: entries -> if i = j then entries else BVar j :: go i entries
  | Var _ :: entries -> go i entries
  | Def _ :: entries -> go i entries
  in
  match r with
  | D.BVar i -> (go i entries, range)

let read_back_level (entries, _) x =
  let rec go acc = function
    | BVar i :: entries -> if i = x then acc else go (acc + 1) entries
    | Var {level; _} :: entries -> if level = x then acc else go (acc + 1) entries
    | Def _ :: entries -> go (acc + 1) entries
    | [] -> raise Removed
  in
  go 0 entries

let do_stack root_inst rootf =
  let rec go env = function
    | D.Root t0 -> rootf env t0
    | D.Ap (s, Normal {term;_}) -> E.do_ap (get_range env) (go env s) term
    | D.NRec (tp, zero, suc, s) -> E.do_rec (get_range env) tp zero suc (go env s)
    | D.Fst s -> E.do_fst (go env s)
    | D.Snd s -> E.do_snd (get_range env) (go env s)
    | D.BApp (s, i) ->
      let env = restrict_env (D.BVar i) env in
      E.do_bapp (get_range env) (go env s) (D.BVar i)
    | D.J (mot, refl, _, _, _, s) -> E.do_j (get_range env) mot refl (go env s)
    | D.Ungel (_, mot, i, s, clo, case) ->
      let (i, s, env) = expose root_inst i s env in
      E.do_ungel (get_range env) mot i (go env s) clo case
  in
  go

exception Cannot_reduce_extent

let rec reduce_extent_root env (D.Ext {var = i; dom; ctx; varcase; _}) =
  let restricted_env = restrict_env (D.BVar i) env in
  let i_env = add_bvar i restricted_env in
  let dom_i = E.do_bclos (get_range i_env) dom (D.BVar i) in
  (* let ctx' = read_back_nf env (D.Normal {tp = dom_i; term = ctx}) in
   * let i' = read_back_level env i in *)
  let result =
    try
      Some (read_back_nf i_env (D.Normal {tp = dom_i; term = ctx}))
    with
      Removed -> None
  in
  begin
    match result with
    | Some extract ->
      let extract_blam =
        D.BLam (D.Clos {term = extract; env = env_to_sem_env restricted_env}) in
      let output_varcase = E.do_closbclos (get_range env) varcase extract_blam (D.BVar i) in
      output_varcase
    | _ -> raise Cannot_reduce_extent
  end

and reduce_extent env stack =
    try
      Some (do_stack D.instantiate_extent_root reduce_extent_root env stack)
    with
      Cannot_reduce_extent -> None

and read_back_nf env nf =
  match nf with
  (* Functions *)
  | D.Normal {tp = D.Pi (src, dest); term = f} ->
    let (arg, arg_env) = mk_var src env in
    let nf = D.Normal
        {tp = E.do_clos (get_range arg_env) dest arg;
         term = E.do_ap (get_range arg_env) f arg} in
    Syn.Lam (read_back_nf arg_env nf)
  (* Pairs *)
  | D.Normal {tp = D.Sg (fst, snd); term = p} ->
     let fst' = E.do_fst p in
     let snd = E.do_clos (get_range env) snd fst' in
     let snd' = E.do_snd (get_range env) p in
     Syn.Pair
       (read_back_nf env (D.Normal {tp = fst; term = fst'}),
        read_back_nf env (D.Normal {tp = snd; term = snd'}))
  (* Numbers *)
  | D.Normal {tp = D.Nat; term = D.Zero} -> Syn.Zero
  | D.Normal {tp = D.Nat; term = D.Suc nf} ->
     Syn.Suc (read_back_nf env (D.Normal {tp = D.Nat; term = nf}))
  (* Bridge *)
  | D.Normal {tp = D.Bridge dest; term} ->
     let (arg, arg_env) = mk_bvar env in
     let nf = D.Normal
         {tp = E.do_bclos (get_range arg_env) dest arg;
          term = E.do_bapp (get_range arg_env) term arg} in
     Syn.BLam (read_back_nf arg_env nf)
  (* Id *)
  | D.Normal {tp = D.Id (tp, _, _); term = D.Refl term} ->
     Syn.Refl (read_back_nf env (D.Normal {tp; term}))
  (* Gel *)
  | D.Normal {tp = D.Gel (_, tp); term = D.Engel (i, t)} ->
    let i' = read_back_level env i in
    let env = restrict_env (D.BVar i) env in
    Syn.Engel (Syn.BVar i', read_back_nf env (D.Normal {tp; term = t}))
  (* Types *)
  | D.Normal {tp = D.Uni _; term = t} -> read_back_tp env t
  (* Extent type *)
  | D.Normal {tp = D.Extent {term = tp_stack; _}; term} ->
    begin
      match reduce_extent env tp_stack with
      | Some tp -> read_back_nf env (D.Normal {tp; term})
      | None -> read_back_neutral_or_extent env term
    end
  | D.Normal {tp = _; term} -> read_back_neutral_or_extent env term

and read_back_tp env d =
  match d with
  | D.Nat -> Syn.Nat
  | D.Pi (src, dest) ->
    let (arg, arg_env) = mk_var src env in
    Syn.Pi (read_back_tp env src, read_back_tp arg_env (E.do_clos (get_range arg_env) dest arg))
  | D.Sg (fst, snd) ->
    let (arg, arg_env) = mk_var fst env in
    Syn.Sg (read_back_tp env fst, read_back_tp arg_env (E.do_clos (get_range arg_env) snd arg))
  | D.Bridge dest ->
    let (arg, arg_env) = mk_bvar env in
    Syn.Bridge (read_back_tp arg_env (E.do_bclos (get_range arg_env) dest arg))
  | D.Id (tp, left, right) ->
    Syn.Id
      (read_back_tp env tp,
       read_back_nf env (D.Normal {tp; term = left}),
       read_back_nf env (D.Normal {tp; term = right}))
  | D.Gel (i, t) ->
    let i' = read_back_level env i in
    let env = restrict_env (D.BVar i) env in
    Syn.Gel (Syn.BVar i', read_back_tp env t)
  | D.Uni k -> Syn.Uni k
  | _ -> read_back_neutral_or_extent env d

and read_back_neutral_or_extent env term =
  match term with
  | D.Neutral {term = ne; _} ->
    read_back_stack D.instantiate_bvar (fun env x -> Syn.Var (read_back_level env x)) env ne
  | D.Extent {tp; term} ->
    begin
      match reduce_extent env term with
      | Some term -> read_back_nf env (D.Normal {tp; term})
      | None -> read_back_stack D.instantiate_extent_root read_back_extent_root env term
    end
  | _ -> raise (Quote_failed "Ill-typed read_back_neutral_or_extent")

and read_back_stack
  : 'a. (int -> int -> 'a -> 'a) -> (env -> 'a -> Syntax.t) -> env -> 'a D.stack -> Syntax.t =
  fun root_inst rootf ->
  let rec go env = function
    | D.Root x -> rootf env x
    | D.Ap (s, arg) ->
      Syn.Ap (go env s, read_back_nf env arg)
    | D.NRec (tp, zero, suc, s) ->
      let (nat_arg, nat_env) = mk_var D.Nat env in
      let applied_tp = E.do_clos (get_range nat_env) tp nat_arg in
      let tp' = read_back_tp nat_env applied_tp in
      let zero_tp = E.do_clos (get_range env) tp D.Zero in
      let zero' = read_back_nf env (D.Normal {tp = zero_tp; term = zero}) in
      let (suc_arg, suc_env) = mk_var applied_tp nat_env in
      let applied_suc_tp = E.do_clos (get_range suc_env) tp (D.Suc nat_arg) in
      let applied_suc = E.do_clos2 (get_range suc_env) suc nat_arg suc_arg in
      let suc' = read_back_nf suc_env (D.Normal {tp = applied_suc_tp; term = applied_suc}) in
      Syn.NRec
        (tp', zero', suc', go env s)
    | D.Fst s -> Syn.Fst (go env s)
    | D.Snd s -> Syn.Snd (go env s)
    | D.BApp (s, i) ->
      let i' = read_back_level env i in
      let env = restrict_env (D.BVar i) env in
      Syn.BApp (go env s, Syn.BVar i')
    | D.J (mot, refl, tp, left, right, s) ->
      let (mot_arg1, mot_env1) = mk_var tp env in
      let (mot_arg2, mot_env2) = mk_var tp mot_env1 in
      let (mot_arg3, mot_env3) = mk_var (D.Id (tp, left, right)) mot_env2 in
      let mot_syn =
        read_back_tp mot_env3 (E.do_clos3 (get_range mot_env3) mot mot_arg1 mot_arg2 mot_arg3) in
      let (refl_arg, refl_env) = mk_var tp env in
      let refl_syn =
        read_back_nf
          refl_env
          (D.Normal
             {term = E.do_clos (get_range refl_env) refl refl_arg;
              tp = E.do_clos3 (get_range refl_env) mot refl_arg refl_arg (D.Refl refl_arg)}) in
      Syn.J (mot_syn, refl_syn, go env s)
    | D.Ungel (tp, mot, i, s, _, case) ->
      let sem_env = env_to_sem_env env in
      let mot_inner_tp = Syn.Gel (Syn.BVar 0, read_back_tp env tp) in
      let (mot_arg, mot_env) =
        mk_var (D.Bridge (D.Clos {term = mot_inner_tp; env = sem_env})) env in
      let mot' = read_back_tp mot_env (E.do_clos (get_range mot_env) mot mot_arg) in
      let (case_arg, case_env) = mk_var tp env in
      let mot_gel =
        D.BLam
          (D.Clos
             {term = Syn.Engel (Syn.BVar 0, Syn.Var 0);
              env = env_to_sem_env case_env})
      in
      let case' = read_back_nf
          case_env
          (D.Normal
             {term = E.do_clos (get_range case_env) case case_arg;
              tp = E.do_clos (get_range case_env) mot mot_gel}) in
      let (_, s, env) = expose root_inst i s env in
      Syn.Ungel (mot', go env s, case')
  in
  go

and read_back_extent_root env (D.Ext {var = i; dom; mot; ctx; varcase}) =
  let i' = read_back_level env i in
  let restricted_env = restrict_env (D.BVar i) env in
  let (barg, benv) = mk_bvar restricted_env in
  let applied_dom = E.do_bclos (get_range benv) dom barg in
  let dom' = read_back_tp benv applied_dom in
  let (dom_arg, dom_env) = mk_var applied_dom benv in
  let applied_mot = E.do_bclosclos (get_range dom_env) mot barg dom_arg in
  let mot' = read_back_tp dom_env applied_mot in
  let dom_i = E.do_bclos (get_range env) dom (D.BVar i) in
  let ctx' = read_back_nf env (D.Normal {tp = dom_i; term = ctx}) in
  let (bridge_arg, bridge_env) = mk_var (D.Bridge dom) restricted_env in
  let (varcase_barg, varcase_benv) = mk_bvar bridge_env in
  let varcase_inst = E.do_bapp (get_range varcase_benv) bridge_arg varcase_barg in
  let varcase_mot = E.do_bclosclos (get_range varcase_benv) mot varcase_barg varcase_inst in
  let applied_varcase = E.do_closbclos (get_range varcase_benv) varcase bridge_arg varcase_barg in
  let varcase' =
    read_back_nf varcase_benv (D.Normal {tp = varcase_mot; term = applied_varcase})
  in
  Syn.Extent (Syn.BVar i', dom', mot', ctx', varcase')

let rec check_nf env nf1 nf2 =
  match nf1, nf2 with
  (* Functions *)
  | D.Normal {tp = D.Pi (src1, dest1); term = f1},
    D.Normal {tp = D.Pi (_, dest2); term = f2} ->
    let (arg, arg_env) = mk_var src1 env in
    let range = get_range arg_env in
    let nf1 = D.Normal {tp = E.do_clos range dest1 arg; term = E.do_ap range f1 arg} in
    let nf2 = D.Normal {tp = E.do_clos range dest2 arg; term = E.do_ap range f2 arg} in
    check_nf arg_env nf1 nf2
  (* Pairs *)
  | D.Normal {tp = D.Sg (fst1, snd1); term = p1},
    D.Normal {tp = D.Sg (fst2, snd2); term = p2} ->
    let range = get_range env in
    let p11, p21 = E.do_fst p1, E.do_fst p2 in
    let snd1, snd2 = E.do_clos range snd1 p11, E.do_clos range snd2 p21 in
    let p12, p22 = E.do_snd range p1, E.do_snd range p2 in
    check_nf env (D.Normal {tp = fst1; term = p11}) (D.Normal {tp = fst2; term = p21})
    && check_nf env (D.Normal {tp = snd1; term = p12}) (D.Normal {tp = snd2; term = p22})
  (* Numbers *)
  | D.Normal {tp = D.Nat; term = D.Zero},
    D.Normal {tp = D.Nat; term = D.Zero} -> true
  | D.Normal {tp = D.Nat; term = D.Suc nf1},
    D.Normal {tp = D.Nat; term = D.Suc nf2} ->
    check_nf env (D.Normal {tp = D.Nat; term = nf1}) (D.Normal {tp = D.Nat; term = nf2})
  (* Id *)
  | D.Normal {tp = D.Id (tp, _, _); term = D.Refl term1},
    D.Normal {tp = D.Id (_, _, _); term = D.Refl term2} ->
    check_nf env (D.Normal {tp; term = term1}) (D.Normal {tp; term = term2})
  (* Bridge *)
  | D.Normal {tp = D.Bridge dest1; term = p1},
    D.Normal {tp = D.Bridge dest2; term = p2} ->
    let (arg, arg_env) = mk_bvar env in
    let range = get_range arg_env in
    let nf1 = D.Normal {tp = E.do_bclos range dest1 arg; term = E.do_bapp range p1 arg} in
    let nf2 = D.Normal {tp = E.do_bclos range dest2 arg; term = E.do_bapp range p2 arg} in
    check_nf arg_env nf1 nf2
  (* Gel *)
  | D.Normal {tp = D.Gel (_, tp1); term = D.Engel (i1, t1)},
    D.Normal {tp = D.Gel (_, tp2); term = D.Engel (_, t2)} ->
    let env = restrict_env (D.BVar i1) env in
    check_nf env (D.Normal {tp = tp1; term = t1}) (D.Normal {tp = tp2; term = t2})
  (* Types *)
  | D.Normal {tp = D.Uni _; term = t1}, D.Normal {tp = D.Uni _; term = t2} ->
    check_tp ~subtype:false env t1 t2
  (* Extent type on the left *)
  | D.Normal {tp = D.Extent {term = tp_stack1; _}; term = term1}, _ ->
    begin
      match reduce_extent env tp_stack1 with
      | Some tp1 -> check_nf env (D.Normal {tp = tp1; term = term1}) nf2
      | None ->
        begin
          match nf2 with
          | D.Normal {tp = D.Extent {term = tp_stack2; _}; term = term2} ->
            begin
              match reduce_extent env tp_stack2 with
              | Some tp2 -> check_nf env nf1 (D.Normal {tp = tp2; term = term2})
              | None -> check_neutral_or_extent env term1 term2
            end
          | _ -> false
        end
    end
  | D.Normal {tp = _; term = term1}, D.Normal {tp = _; term = term2} ->
    check_neutral_or_extent env term1 term2

and check_neutral_or_extent env term1 term2 =
  match term1, term2 with
  (* Neutral *)
  | D.Neutral {term = ne1; _}, D.Neutral {term = ne2; _} ->
    check_stack D.instantiate_bvar (fun _ x y -> x = y) env ne1 ne2
  (* Extent term on the left *)
  | D.Extent {term = stack1; tp = tp1}, _ ->
    begin
      match reduce_extent env stack1 with
      | Some term1 ->
        check_nf env (D.Normal {tp = tp1; term = term1}) (D.Normal {tp = tp1; term = term2})
      | None ->
        begin
          match term2 with
          | D.Extent {term = stack2; tp = tp2} ->
            begin
              match reduce_extent env stack2 with
              | Some term2 ->
                check_nf env (D.Normal {tp = tp2; term = term1}) (D.Normal {tp = tp2; term = term2})
              | None -> check_stack D.instantiate_extent_root check_extent_root env stack1 stack2
            end
          | _ -> false
        end
    end
  (* Extent term on the right *)
  | _, D.Extent {term = stack2; tp = tp2} ->
    begin
      match reduce_extent env stack2 with
      | Some term2 ->
        check_nf env (D.Normal {tp = tp2; term = term1}) (D.Normal {tp = tp2; term = term2})
      | None ->
        begin
          match term1 with
          | D.Extent {term = stack1; tp = _} ->
            check_stack D.instantiate_extent_root check_extent_root env stack1 stack2
          | _ -> false
        end
    end
  | _ -> false

and check_stack
  : 'a. (int -> int -> 'a -> 'a) -> (env -> 'a -> 'a -> bool) -> env -> 'a D.stack -> 'a D.stack -> bool =
  fun root_inst rootf ->
  let rec go env s1 s2 =
    match s1, s2 with
    | D.Root x, D.Root y -> rootf env x y
    | D.Ap (s1, arg1), D.Ap (s2, arg2) ->
      go env s1 s2 && check_nf env arg1 arg2
    | D.NRec (tp1, zero1, suc1, n1), D.NRec (tp2, zero2, suc2, n2) ->
      let (nat_arg, nat_env) = mk_var D.Nat env in
      let applied_tp1 = E.do_clos (get_range nat_env) tp1 nat_arg in
      let applied_tp2 = E.do_clos (get_range nat_env) tp2 nat_arg in
      check_tp ~subtype:false nat_env applied_tp1 applied_tp2 &&
      let zero_tp = E.do_clos (get_range env) tp1 D.Zero in
      check_nf env (D.Normal {tp = zero_tp; term = zero1}) (D.Normal {tp = zero_tp; term = zero2}) &&
      let (suc_arg, suc_env) = mk_var applied_tp1 nat_env in
      let applied_suc_tp = E.do_clos (get_range suc_env) tp1 (D.Suc nat_arg) in
      let applied_suc1 = E.do_clos2 (get_range suc_env) suc1 nat_arg suc_arg in
      let applied_suc2 = E.do_clos2 (get_range suc_env) suc2 nat_arg suc_arg in
      check_nf suc_env
        (D.Normal {tp = applied_suc_tp; term = applied_suc1})
        (D.Normal {tp = applied_suc_tp; term = applied_suc2}) &&
      go env n1 n2
    | D.Fst s1, D.Fst s2  -> go env s1 s2
    | D.Snd s1, D.Snd s2 -> go env s1 s2
    | D.BApp (s1, i1), D.BApp (s2, i2) ->
      i1 = i2 &&
      go (restrict_env (D.BVar i1) env) s1 s2
    | D.J (mot1, refl1, tp1, left1, right1, eq1),
      D.J (mot2, refl2, tp2, left2, right2, eq2) ->
      check_tp ~subtype:false env tp1 tp2 &&
      check_nf env (D.Normal {tp = tp1; term = left1}) (D.Normal {tp = tp2; term = left2}) &&
      check_nf env (D.Normal {tp = tp1; term = right1}) (D.Normal {tp = tp2; term = right2}) &&
      let (mot_arg1, mot_env1) = mk_var tp1 env in
      let (mot_arg2, mot_env2) = mk_var tp1 mot_env1 in
      let (mot_arg3, mot_env3) = mk_var (D.Id (tp1, left1, right1)) mot_env2 in
      check_tp ~subtype:false mot_env3
        (E.do_clos3 (get_range mot_env3) mot1 mot_arg1 mot_arg2 mot_arg3)
        (E.do_clos3 (get_range mot_env3) mot2 mot_arg1 mot_arg2 mot_arg3) &&
      let (refl_arg, refl_env) = mk_var tp1 env in
      check_nf
        refl_env
        (D.Normal
           {term = E.do_clos (get_range refl_env) refl1 refl_arg;
            tp = E.do_clos3 (get_range refl_env) mot1 refl_arg refl_arg (D.Refl refl_arg)})
        (D.Normal
           {term = E.do_clos (get_range refl_env) refl2 refl_arg;
            tp = E.do_clos3 (get_range refl_env) mot2 refl_arg refl_arg (D.Refl refl_arg)}) &&
      go env eq1 eq2
    | D.Ungel (tp1, mot1, i1, s1, _, case1),
      D.Ungel (_, mot2, i2, s2, _, case2) ->
      let sem_env = env_to_sem_env env in
      let mot_inner_tp = Syn.Gel (Syn.BVar 0, read_back_tp env tp1) in
      let (mot_arg, mot_env) =
        mk_var (D.Bridge (D.Clos {term = mot_inner_tp; env = sem_env})) env in
      check_tp ~subtype:false mot_env
        (E.do_clos (get_range mot_env) mot1 mot_arg)
        (E.do_clos (get_range mot_env) mot2 mot_arg) &&
      let (case_arg, case_env) = mk_var tp1 env in
      let mot_gel =
        D.BLam (D.Clos {term = Syn.Engel (Syn.BVar 0, Syn.Var 0); env = env_to_sem_env case_env}) in
      check_nf case_env
        (D.Normal
           {term = E.do_clos (get_range case_env) case1 case_arg;
            tp = E.do_clos (get_range case_env) mot1 mot_gel})
        (D.Normal
           {term = E.do_clos (get_range case_env) case2 case_arg;
            tp = E.do_clos (get_range case_env) mot2 mot_gel}) &&
      let (_, s1, _) = expose root_inst i1 s1 env in
      let (_, s2, env) = expose root_inst i2 s2 env in
      go env s1 s2
    | _ -> false
  in
  go

and check_extent_root env
    (D.Ext {var = i1; dom = dom1; mot = mot1; ctx = ctx1; varcase = varcase1})
    (D.Ext {var = i2; dom = dom2; mot = mot2; ctx = ctx2; varcase = varcase2})
  =
  i1 = i2 &&
  let restricted_env = restrict_env (D.BVar i1) env in
  let (barg, benv) = mk_bvar restricted_env in
  let applied_dom1 = E.do_bclos (get_range benv) dom1 barg in
  let applied_dom2 = E.do_bclos (get_range benv) dom2 barg in
  check_tp ~subtype:false benv applied_dom1 applied_dom2 &&
  let (dom_arg, dom_env) = mk_var applied_dom1 benv in
  let applied_mot1 = E.do_bclosclos (get_range dom_env) mot1 barg dom_arg in
  let applied_mot2 = E.do_bclosclos (get_range dom_env) mot2 barg dom_arg in
  check_tp ~subtype:false dom_env applied_mot1 applied_mot2 &&
  let dom_i = E.do_bclos (get_range env) dom1 (D.BVar i1) in
  check_nf env (D.Normal {tp = dom_i; term = ctx1}) (D.Normal {tp = dom_i; term = ctx2}) &&
  let (bridge_arg, bridge_env) = mk_var (D.Bridge dom1) restricted_env in
  let (varcase_barg, varcase_benv) = mk_bvar bridge_env in
  let varcase_inst = E.do_bapp (get_range varcase_benv) bridge_arg varcase_barg in
  let varcase_mot = E.do_bclosclos (get_range varcase_benv) mot1 varcase_barg varcase_inst in
  let applied_varcase1 = E.do_closbclos (get_range varcase_benv) varcase1 bridge_arg varcase_barg in
  let applied_varcase2 = E.do_closbclos (get_range varcase_benv) varcase2 bridge_arg varcase_barg in
  check_nf varcase_benv
    (D.Normal {tp = varcase_mot; term = applied_varcase1})
    (D.Normal {tp = varcase_mot; term = applied_varcase2})

and check_tp ~subtype env d1 d2 =
  match d1, d2 with
  | D.Nat, D.Nat -> true
  | D.Id (tp1, left1, right1), D.Id (tp2, left2, right2) ->
    check_tp ~subtype env tp1 tp2 &&
    check_nf env (D.Normal {tp = tp1; term = left1}) (D.Normal {tp = tp1; term = left2}) &&
    check_nf env (D.Normal {tp = tp1; term = right1}) (D.Normal {tp = tp1; term = right2})
  | D.Pi (src, dest), D.Pi (src', dest') ->
    let (arg, arg_env) = mk_var src' env in
    check_tp ~subtype env src' src &&
    check_tp ~subtype arg_env
      (E.do_clos (get_range arg_env) dest arg)
      (E.do_clos (get_range arg_env) dest' arg)
  | D.Sg (fst, snd), D.Sg (fst', snd') ->
    let (arg, arg_env) = mk_var fst env in
    check_tp ~subtype env fst fst' &&
    check_tp ~subtype arg_env
      (E.do_clos (get_range arg_env) snd arg)
      (E.do_clos (get_range arg_env) snd' arg)
  | D.Bridge dest, D.Bridge dest' ->
    let (barg, barg_env) = mk_bvar env in
    check_tp ~subtype barg_env
      (E.do_bclos (get_range barg_env) dest barg)
      (E.do_bclos (get_range barg_env) dest' barg)
  | D.Gel (i, t), D.Gel (i', t') ->
    i = i' &&
    check_tp ~subtype (restrict_env (D.BVar i) env) t t'
  | D.Uni k, D.Uni j -> if subtype then k <= j else k = j
  | _ -> check_neutral_or_extent env d1 d2
