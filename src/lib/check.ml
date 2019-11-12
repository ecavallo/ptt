(* This file implements the semantic type-checking algorithm described in the paper. *)
module D = Domain
module Syn = Syntax
module E = Eval
module Q = Quote

type env_entry =
  | DVar of {level : D.lvl; width : int}
  | Var of {level : D.lvl; tp : D.t}
  | Def of {term : D.t; tp : D.t}
  | Restrict of Syn.idx
[@@deriving show, eq]
type env = env_entry list
[@@deriving show, eq]

type error =
    Cannot_synth_term of Syn.t
  | Dim_mismatch of D.dim * D.dim
  | Type_mismatch of D.t * D.t
  | Expecting_universe of D.t
  | Expecting_term of D.lvl
  | Misc of string

let pp_error fmt = function
  | Cannot_synth_term t ->
    Format.fprintf fmt "@[<v> Cannot synthesize the type of: @[<hov 2>  ";
    Syn.pp fmt t;
    Format.fprintf fmt "@]@]@,"
  | Dim_mismatch (b1, b2) ->
    Format.fprintf fmt "@[<v>Cannot equate@,@[<hov 2>  ";
    D.pp_dim fmt b1;
    Format.fprintf fmt "@]@ with@,@[<hov 2>  ";
    D.pp_dim fmt b2;
    Format.fprintf fmt "@]@]@,"
  | Type_mismatch (t1, t2) ->
    Format.fprintf fmt "@[<v>Cannot equate@,@[<hov 2>  ";
    D.pp fmt t1;
    Format.fprintf fmt "@]@ with@,@[<hov 2>  ";
    D.pp fmt t2;
    Format.fprintf fmt "@]@]@,"
  | Expecting_universe d ->
    Format.fprintf fmt "@[<v>Expected some universe but found@ @[<hov 2>";
    D.pp fmt d;
    Format.fprintf fmt "@]@]@,"
  | Expecting_term j ->
    Format.fprintf fmt "@[<v>Expected term variable but found dimension@ @[<hov 2>";
    Format.pp_print_int fmt j;
    Format.fprintf fmt "@]@]@,"
  | Misc s -> Format.pp_print_string fmt s

exception Type_error of error

let tp_error e = raise (Type_error e)

let rec env_to_sem_env = function
  | [] -> []
  | DVar {level; _} :: env -> D.Dim (D.DVar level) :: env_to_sem_env env
  | Var {level; tp} :: env -> D.Term (D.Neutral {tp; term = D.root (D.Var level)}) :: env_to_sem_env env
  | Def {term; _} :: env -> D.Term term :: env_to_sem_env env
  | Restrict _ :: env -> env_to_sem_env env

let rec env_to_quote_env = function
  | [] -> []
  | DVar {level; _} :: env -> Q.DVar level :: env_to_quote_env env
  | Var {level; tp} :: env -> Q.Var {level; tp} :: env_to_quote_env env
  | Def {term; _} :: env -> Q.Def term :: env_to_quote_env env
  | Restrict _ :: env -> env_to_quote_env env

let rec synth_var env x =
  match x, env with
  | _, [] -> tp_error (Misc "Tried to access non-existent variable\n")
  | x, Restrict j :: env ->
    if x < j
    then tp_error (Misc "Tried to use restricted term variable\n")
    else synth_var env x
  | 0, Var {tp; _} :: _ -> tp
  | 0, Def {tp; _} :: _ -> tp
  | 0, DVar {level; _} :: _ -> tp_error (Expecting_term level)
  | x, _ :: env -> synth_var env (x - 1)

let mk_bvar width env size =
  (D.DVar size, DVar {level = size; width} :: env)

let mk_var tp env size =
  (D.Neutral {tp; term = D.root (D.Var size)}, Var {level = size; tp} :: env)

let mk_vars tps env size =
  (List.mapi (fun i tp -> D.Neutral {tp; term = D.root (D.Var (size + i))}) tps,
   List.rev_append
     (List.mapi (fun i tp -> Var {level = size + i; tp}) tps)
     env)

let restrict_env r env =
  match r with
  | Syn.DVar i -> Restrict i :: env
  | Syn.Const _ -> env

let assert_subtype env size t1 t2 =
  if Q.check_tp ~subtype:true env size t1 t2
  then ()
  else tp_error (Type_mismatch (t1, t2))

let assert_equal env size t1 t2 tp =
  if Q.check_nf env size (D.Normal {tp; term = t1}) (D.Normal {tp; term = t2})
  then ()
  else tp_error (Type_mismatch (t1, t2))

let assert_dim_equal b1 b2 =
  if b1 = b2 then ()
  else tp_error (Dim_mismatch (b1, b2))

let check_dim ~env ~dim ~width =
  let rec go i env =
    match i, env with
    | _, [] -> tp_error (Misc "Tried to access non-existent variable\n")
    | i, Restrict j :: env ->
      if i = j
      then tp_error (Misc "Tried to use restricted dimension\n")
      else go i env
    | 0, DVar {width = w; _} :: _ ->
      if width = w
      then ()
      else tp_error (Misc "Dimension width mismatch\n")
    | 0, _ :: _ -> tp_error (Misc "Expected bridge dimension\n")
    | i, _ :: env -> go (i - 1) env
  in
  match dim with
  | Syn.DVar i -> go i env
  | Syn.Const o ->
    if o < width
    then ()
    else tp_error (Misc "Dimension constant out of bounds\n")

let rec check ~env ~size ~term ~tp =
  match tp with
  | D.Neutral {term = (D.Ext e, tp_spine); _} ->
    begin
      match Q.reduce_extent (env_to_quote_env env) size (e, tp_spine) with
      | Some tp -> check ~env ~size ~term ~tp
      | None -> check_inert ~env ~size ~term ~tp
    end
  | _ -> check_inert ~env ~size ~term ~tp

and check_inert ~env ~size ~term ~tp =
  match term with
  | Syn.Let (def, body) ->
    let def_tp = synth ~env ~size ~term:def in
    let def_val = E.eval def (env_to_sem_env env) size in
    check ~env:(Def {term = def_val; tp = def_tp} :: env) ~size ~term:body ~tp
  | Unit ->
    begin
      match tp with
      | D.Uni _ -> ()
      | t -> tp_error (Expecting_universe t)
    end
  | Nat ->
    begin
      match tp with
      | D.Uni _ -> ()
      | t -> tp_error (Expecting_universe t)
    end
  | Bool ->
    begin
      match tp with
      | D.Uni _ -> ()
      | t -> tp_error (Expecting_universe t)
    end
  | Id (tp', l, r) ->
    begin
      match tp with
      | D.Uni _ ->
        check ~env ~size ~term:tp' ~tp;
        let tp' = E.eval tp' (env_to_sem_env env) size in
        check ~env ~size ~term:l ~tp:tp';
        check ~env ~size ~term:r ~tp:tp'
      | t -> tp_error (Expecting_universe t)
    end
  | Refl term ->
    begin
      match tp with
      | D.Id (tp, left, right) ->
        check ~env ~size ~term ~tp;
        let quote_env = env_to_quote_env env in
        let sem_env = Q.env_to_sem_env quote_env in
        let term = E.eval term sem_env size in
        assert_equal quote_env size term left tp;
        assert_equal quote_env size term right tp
      | t -> tp_error (Misc ("Expecting Id but found\n" ^ D.show t))
    end
  | Pi (l, r) | Sg (l, r) ->
    begin
      match tp with
      | D.Uni _ ->
        check ~env ~size ~term:l ~tp;
        let l_sem = E.eval l (env_to_sem_env env) size in
        let (_, arg_env) = mk_var l_sem env size in
        check ~env:arg_env ~size:(size + 1) ~term:r ~tp
      | t -> tp_error (Expecting_universe t)
    end
  | Lam body ->
    begin
      match tp with
      | D.Pi (arg_tp, clos) ->
        let (arg, arg_env) = mk_var arg_tp env size in
        let dest_tp = E.do_clos (size + 1) clos (D.Term arg) in
        check ~env:arg_env ~size:(size + 1) ~term:body ~tp:dest_tp;
      | t -> tp_error (Misc ("Expecting Pi but found\n" ^ D.show t))
    end
  | Pair (left, right) ->
    begin
      match tp with
      | D.Sg (left_tp, right_tp) ->
        check ~env ~size ~term:left ~tp:left_tp;
        let left_sem = E.eval left (env_to_sem_env env) size in
        check ~env ~size ~term:right ~tp:(E.do_clos size right_tp (D.Term left_sem))
      | t -> tp_error (Misc ("Expecting Sg but found\n" ^ D.show t))
    end
  | Bridge (term, ends) ->
    begin
      match tp with
      | Uni _ ->
        let width = List.length ends in
        let (_, arg_env) = mk_bvar width env size in
        check ~env:arg_env ~size:(size + 1) ~term ~tp;
        let width = List.length ends in
        let tps = E.do_consts size (D.Clos {term; env = env_to_sem_env env}) width in
        List.iter2 (fun term tp -> check ~env ~size ~term ~tp) ends tps
      | t -> tp_error (Expecting_universe t)
    end
  | BLam body ->
    begin
      match tp with
      | Bridge (clos, ends) ->
        let width = List.length ends in
        let (arg, arg_env) = mk_bvar width env size in
        let dest_tp = E.do_clos (size + 1) clos (D.Dim arg) in
        check ~env:arg_env ~size:(size + 1) ~term:body ~tp:dest_tp;
        let quote_env = env_to_quote_env env in
        let sem_env = Q.env_to_sem_env quote_env in
        List.iteri
          (fun o pt ->
             let body_o = E.eval body (D.Dim (D.Const o) :: sem_env) size in
             let tp = E.do_clos size clos (D.Dim (D.Const o)) in
             assert_equal quote_env size body_o pt tp)
          ends
      | t -> tp_error (Misc ("Expecting Bridge but found\n" ^ D.show t))
    end
  | Gel (r, ends, rel) ->
    begin
      match tp with
      | Uni _ ->
        let width = List.length ends in
        check_dim ~env ~dim:r ~width;
        let res_env = restrict_env r env in
        List.iter (fun term -> check ~env:res_env ~size ~term ~tp) ends;
        let sem_env = env_to_sem_env res_env in
        let ends' = List.map (fun t -> E.eval t sem_env size) ends in
        let (_, rel_env) = mk_vars ends' res_env size in
        check ~env:rel_env ~size:(size + width) ~term:rel ~tp;
      | t -> tp_error (Expecting_universe t)
    end
  | Engel (r, ts, term) ->
    begin
      match tp with
      | Gel (j, ends, rel) ->
        let width = List.length ts in
        check_dim ~env ~dim:r ~width;
        let sem_env = env_to_sem_env env in
        assert_dim_equal (E.eval_dim r sem_env) (D.DVar j);
        let res_env = restrict_env r env in
        List.iter2 (fun term tp -> check ~env:res_env ~size ~term ~tp) ts ends;
        let ts' = List.map (fun t -> E.eval t sem_env size) ts in
        check ~env:res_env ~size ~term ~tp:(E.do_closN size rel ts')
      | t -> tp_error (Misc ("Expecting Gel but found\n" ^ D.show t))
    end
  | Uni i ->
    begin
      match tp with
      | Uni j when i < j -> ()
      | t ->
        let msg =
          "Expecting universe over " ^ string_of_int i ^ " but found\n" ^ D.show t in
        tp_error (Misc msg)
    end
  | term -> assert_subtype (env_to_quote_env env) size (synth ~env ~size ~term) tp

and synth ~env ~size ~term =
  match term with
  | Syn.Var i -> synth_var env i
  | Check (term, tp') ->
    let tp = E.eval tp' (env_to_sem_env env) size in
    check ~env ~size ~term ~tp;
    tp
  | Triv -> D.Unit
  | Zero -> D.Nat
  | Suc term -> check ~env ~size ~term ~tp:Nat; D.Nat
  | True -> D.Bool
  | False -> D.Bool
  | Fst p ->
    begin
      match synth ~env ~size ~term:p with
      | Sg (left_tp, _) -> left_tp
      | t -> tp_error (Misc ("Expecting Sg but found\n" ^ D.show t))
    end
  | Snd p ->
    begin
      match synth ~env ~size ~term:p with
      | Sg (_, right_tp) ->
        let proj = E.eval (Fst p) (env_to_sem_env env) size in
        E.do_clos size right_tp (D.Term proj)
      | t -> tp_error (Misc ("Expecting Sg but found\n" ^ D.show t))
    end
  | Ap (f, a) ->
    begin
      match synth ~env ~size ~term:f with
      | Pi (src, dest) ->
        check ~env ~size ~term:a ~tp:src;
        let a_sem = E.eval a (env_to_sem_env env) size in
        E.do_clos size dest (D.Term a_sem)
      | t -> tp_error (Misc ("Expecting Pi but found\n" ^ D.show t))
    end
  | NRec (mot, zero, suc, n) ->
    check ~env ~size ~term:n ~tp:Nat;
    let sem_env = env_to_sem_env env in
    let (nat_arg, nat_env) = mk_var Nat env size in
    check_tp ~env:nat_env ~size:(size + 1) ~term:mot;
    let zero_tp = E.eval mot (D.Term D.Zero :: sem_env) size in
    check ~env ~size ~term:zero ~tp:zero_tp;
    let ih_tp = E.eval mot (env_to_sem_env nat_env) (size + 1) in
    let (_, ih_env) = mk_var ih_tp nat_env (size + 1) in
    let suc_tp = E.eval mot (D.Term (Suc nat_arg) :: sem_env) (size + 2) in
    check ~env:ih_env ~size:(size + 2) ~term:suc ~tp:suc_tp;
    E.eval mot (D.Term (E.eval n sem_env size) :: sem_env) size
  | If (mot, tt, ff, b) ->
    check ~env ~size ~term:b ~tp:Bool;
    let sem_env = env_to_sem_env env in
    let (_, bool_env) = mk_var Bool env size in
    check_tp ~env:bool_env ~size:(size + 1) ~term:mot;
    let tt_tp = E.eval mot (D.Term D.True :: sem_env) size in
    check ~env ~size ~term:tt ~tp:tt_tp;
    let ff_tp = E.eval mot (D.Term D.False :: sem_env) size in
    check ~env ~size ~term:ff ~tp:ff_tp;
    E.eval mot (D.Term (E.eval b sem_env size) :: sem_env) size
  | BApp (term, r) ->
    let restricted_env = restrict_env r env in
    begin
      match synth ~env:restricted_env ~size ~term with
      | Bridge (clos, ends) ->
        let width = List.length ends in
        check_dim ~width ~env ~dim:r;
        let r' = E.eval_dim r (env_to_sem_env env) in
        E.do_clos size clos (D.Dim r')
      | t -> tp_error (Misc ("Expecting Bridge but found\n" ^ D.show t ^ "\n" ^ Syn.show term))
    end
  | J (mot, refl, eq) ->
    begin
      match synth ~env ~size ~term:eq with
      | D.Id (tp', left, right) ->
        let sem_env = env_to_sem_env env in
        let (mot_arg1, mot_env1) = mk_var tp' env size in
        let (mot_arg2, mot_env2) = mk_var tp' mot_env1 (size + 1) in
        let (_, mot_env3) = mk_var (D.Id (tp', mot_arg1, mot_arg2)) mot_env2 (size + 2) in
        check_tp ~env:mot_env3 ~size:(size + 3) ~term:mot;
        let refl_tp =
          E.eval mot
            (D.Term (D.Refl mot_arg1) :: D.Term mot_arg1 :: D.Term mot_arg1 :: sem_env)
            (size + 1) in
        check ~env:mot_env1 ~size:(size + 1) ~term:refl ~tp:refl_tp;
        E.eval mot (D.Term (E.eval eq sem_env size) :: D.Term right :: D.Term left :: sem_env) size
      | t -> tp_error (Misc ("Expecting Id but found\n" ^ D.show t))
    end
  | Extent (r, dom, mot, ctx, endcase, varcase) ->
    let width = List.length endcase in
    check_dim ~env ~dim:r ~width;
    let sem_env = env_to_sem_env env in
    let r' = E.eval_dim r sem_env in
    let res_env = restrict_env r env in
    let (_, dim_env) = mk_bvar width res_env size in
    check_tp ~env:dim_env ~size:(size + 1) ~term:dom;
    let dom' = E.eval dom (env_to_sem_env dim_env) (size + 1) in
    let (_, dom_env) = mk_var dom' dim_env (size + 1) in
    check_tp ~env:dom_env ~size:(size + 2) ~term:mot;
    let dom_r = E.eval dom (D.Dim r' :: sem_env) size in
    check ~env ~size ~term:ctx ~tp:dom_r;
    List.iteri
      (fun o case ->
         let dom_o = E.eval dom (D.Dim (D.Const o) :: sem_env) size in
         let (case_arg, case_env) = mk_var dom_o res_env size in
         let mot_o = E.eval mot (D.Term case_arg :: D.Dim (D.Const o) :: sem_env) size in
         check ~env:case_env ~size:(size + 1) ~term:case ~tp:mot_o)
      endcase;
    let end_tps = E.do_consts size (D.Clos {term = dom; env = sem_env}) width in
    let (end_vars, ends_env) = mk_vars end_tps res_env size in
    let dom_bridge = D.Bridge (D.Clos {term = dom; env = sem_env}, end_vars) in
    let (bridge_arg, bridge_env) = mk_var dom_bridge ends_env (size + width) in
    let (varcase_barg, varcase_benv) = mk_bvar width bridge_env (size + width + 1) in
    let varcase_inst = E.do_bapp (size + width + 2) bridge_arg varcase_barg in
    let varcase_mot =
      E.eval mot (D.Term varcase_inst :: D.Dim varcase_barg :: sem_env) (size + width + 2) in
    check ~env:varcase_benv ~size:(size + width + 2) ~term:varcase ~tp:varcase_mot;
    E.eval mot (D.Term (E.eval ctx sem_env size) :: D.Dim r' :: sem_env) size
  | Ungel (width, mot, term, case) ->
    let (var_arg, var_env) = mk_bvar width env size in
    begin
      match synth ~env:var_env ~size:(size + 1) ~term with
      | D.Gel (i, end_tps, rel) ->
        assert_dim_equal (D.DVar i) var_arg;
        let sem_env = env_to_sem_env env in
        let end_tms = E.do_consts size (D.Clos {term; env = sem_env}) width in
        let syn_gel =
          Q.read_back_tp (env_to_quote_env var_env) (size + 1) (D.Gel (i, end_tps, rel)) in
        let mot_hyp = D.Bridge (D.Clos {term = syn_gel; env = sem_env}, end_tms) in
        let (_, hyp_env) = mk_var mot_hyp env size in
        check_tp ~env:hyp_env ~size:(size + 1) ~term:mot;
        let applied_rel = E.do_closN size rel end_tms in
        let (wit_arg, wit_env) = mk_var applied_rel env size in
        let (_, gel_env) = mk_bvar width wit_env (size + 1) in
        let syn_engel =
          Q.read_back_nf
            (env_to_quote_env gel_env)
            (size + 2)
            (D.Normal
               {tp = D.Gel (size + 1, end_tps, rel);
                term = D.Engel (size + 1, end_tms, wit_arg)}) in
        let gel_term = D.BLam (D.Clos {term = syn_engel; env = env_to_sem_env wit_env}) in
        let gel_tp = E.eval mot (D.Term gel_term :: sem_env) (size + 1) in
        check ~env:wit_env ~size:(size + 1) ~term:case ~tp:gel_tp;
        E.eval mot (D.Term (D.BLam (D.Clos {term; env = sem_env})) :: sem_env) size
      | t -> tp_error (Misc ("Expecting Gel but found\n" ^ D.show t))
    end
  | _ -> tp_error (Cannot_synth_term term)

and check_tp ~env ~size ~term =
  match term with
  | Syn.Unit -> ()
  | Syn.Nat -> ()
  | Syn.Bool -> ()
  | Uni _ -> ()
  | Bridge (term, ends) ->
    let width = List.length ends in
    let (_, var_env) = mk_bvar width env size in
    check_tp ~env:var_env ~size:(size + 1) ~term;
    let sem_env = env_to_sem_env env in
    List.iteri
      (fun o pt ->
         check ~env ~size ~term:pt ~tp:(E.eval term (D.Dim (D.Const o) :: sem_env) size))
      ends
  | Pi (l, r) | Sg (l, r) ->
    check_tp ~env ~size ~term:l;
    let sem_env = env_to_sem_env env in
    let l_sem = E.eval l sem_env size in
    let (_, var_env) = mk_var l_sem env size in
    check_tp ~env:var_env ~size:(size + 1) ~term:r
  | Let (def, body) ->
    let def_tp = synth ~env ~size ~term:def in
    let def_val = E.eval def (env_to_sem_env env) size in
    check_tp ~env:(Def {term = def_val; tp = def_tp} :: env) ~size ~term:body
  | Id (tp, l, r) ->
    check_tp ~env ~size ~term:tp;
    let tp = E.eval tp (env_to_sem_env env) size in
    check ~env ~size ~term:l ~tp;
    check ~env ~size ~term:r ~tp
  | Gel (r, ends, rel) ->
    let width = List.length ends in
    check_dim ~env ~dim:r ~width;
    let res_env = restrict_env r env in
    let sem_env = env_to_sem_env res_env in
    List.iter (fun term -> check_tp ~env:res_env ~size ~term) ends;
    let ends' = List.map (fun term -> E.eval term sem_env size) ends in
    let (_, rel_env) = mk_vars ends' res_env size in
    check_tp ~env:rel_env ~size:(size + width) ~term:rel
  | term ->
    begin
      match synth ~env ~size ~term with
      | D.Uni _ -> ()
      | t -> tp_error (Expecting_universe t)
    end
