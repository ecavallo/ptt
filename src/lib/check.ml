(* This file implements the semantic type-checking algorithm described in the paper. *)
module D = Domain
module Syn = Syntax
module E = Eval
module Q = Quote

type error =
    Cannot_synth_term of Syn.t
  | BDim_mismatch of D.bdim * D.bdim
  | Type_mismatch of D.t * D.t
  | Expecting_universe of D.t
  | Expecting_term of int
  | Misc of string

let pp_error fmt = function
  | Cannot_synth_term t ->
    Format.fprintf fmt "@[<v> Cannot synthesize the type of: @[<hov 2>  ";
    Syn.pp fmt t;
    Format.fprintf fmt "@]@]@,"
  | BDim_mismatch (b1, b2) ->
    Format.fprintf fmt "@[<v>Cannot equate@,@[<hov 2>  ";
    D.pp_bdim fmt b1;
    Format.fprintf fmt "@]@ with@,@[<hov 2>  ";
    D.pp_bdim fmt b2;
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

let get_tp (entries, _) x =
  match List.nth entries x with
  | Q.BVar j -> tp_error (Expecting_term j)
  | Q.Var {tp; _} -> tp
  | Q.Def {tp; _} -> tp

let assert_subtype env t1 t2 =
  if Q.check_tp ~subtype:true env t1 t2
  then ()
  else tp_error (Type_mismatch (t1, t2))

let assert_equal env t1 t2 tp =
  if Q.check_nf env (D.Normal {tp; term = t1}) (D.Normal {tp; term = t2})
  then ()
  else tp_error (Type_mismatch (t1, t2))

let assert_bdim_equal b1 b2 =
  if b1 = b2 then ()
  else tp_error (BDim_mismatch (b1, b2))

let rec check ~env ~term ~tp =
  match term with
  | Syn.Let (def, body) ->
    let def_tp = synth ~env ~term:def in
    let def_val = E.eval def (Q.env_to_sem_env env) in
    check ~env:(Q.add_def ~term:def_val ~tp:def_tp env) ~term:body ~tp
  | Nat ->
    begin
      match tp with
      | D.Uni _ -> ()
      | t -> tp_error (Expecting_universe t)
    end
  | Id (tp', l, r) ->
    begin
      match tp with
      | D.Uni _ ->
        check ~env ~term:tp' ~tp;
        let tp' = E.eval tp' (Q.env_to_sem_env env) in
        check ~env ~term:l ~tp:tp';
        check ~env ~term:r ~tp:tp'
      | t -> tp_error (Expecting_universe t)
    end
  | Refl term ->
    begin
      match tp with
      | D.Id (tp, left, right) ->
        check ~env ~term ~tp;
        let sem_env = Q.env_to_sem_env env in
        let term = E.eval term sem_env in
        assert_equal env term left tp;
        assert_equal env term right tp
      | t -> tp_error (Misc ("Expecting Id but found\n" ^ D.show t))
    end
  | Pi (l, r) | Sg (l, r) ->
    begin
      match tp with
      | D.Uni _ ->
        check ~env ~term:l ~tp;
        let l_sem = E.eval l (Q.env_to_sem_env env) in
        let (_, arg_env) = Q.mk_var l_sem env in
        check ~env:arg_env ~term:r ~tp
      | t -> tp_error (Expecting_universe t)
    end
  | Lam body ->
    begin
      match tp with
      | D.Pi (arg_tp, clos) ->
        let (arg, arg_env) = Q.mk_var arg_tp env in
        let dest_tp = E.do_clos (Q.get_range arg_env) clos arg in
        check ~env:arg_env ~term:body ~tp:dest_tp;
      | t -> tp_error (Misc ("Expecting Pi but found\n" ^ D.show t))
    end
  | Pair (left, right) ->
    begin
      match tp with
      | D.Sg (left_tp, right_tp) ->
        check ~env ~term:left ~tp:left_tp;
        let left_sem = E.eval left (Q.env_to_sem_env env) in
        check ~env ~term:right ~tp:(E.do_clos (Q.get_range env) right_tp left_sem)
      | t -> tp_error (Misc ("Expecting Sg but found\n" ^ D.show t))
    end
  | Bridge term ->
    begin
      match tp with
      | Uni _ ->
        let (_, arg_env) = Q.mk_bvar env in
        check ~env:arg_env ~term ~tp
      | t -> tp_error (Expecting_universe t)
    end
  | BLam body ->
    begin
      match tp with
      | Bridge clos ->
        let (arg, arg_env) = Q.mk_bvar env in
        let dest_tp = E.do_bclos (Q.get_range arg_env) clos arg in
        check ~env:arg_env ~term:body ~tp:dest_tp
      | t -> tp_error (Misc ("Expecting Bridge but found\n" ^ D.show t))
    end
  | Gel (r, term) ->
    begin
      match tp with
      | Uni _ ->
        let r' = E.eval_bdim r (Q.env_to_sem_env env) in
        check ~env:(Q.restrict_env r' env) ~term ~tp;
      | t -> tp_error (Expecting_universe t)
    end
  | Engel (r, term) ->
    begin
      match r with
      | BVar i ->
        begin
          match tp with
          | Gel (j, tp) ->
            let sem_env = Q.env_to_sem_env env in
            assert_bdim_equal (E.eval_bdim (Syn.BVar i) sem_env) (D.BVar j);
            check ~env:(Q.restrict_env (D.BVar j) env) ~term ~tp
          | t -> tp_error (Misc ("Expecting Gel but found\n" ^ D.show t))
        end
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
  | term -> assert_subtype env (synth ~env ~term) tp

and synth ~env ~term =
  match term with
  | Syn.Var i -> get_tp env i
  | Check (term, tp') ->
    let tp = E.eval tp' (Q.env_to_sem_env env) in
    check ~env ~term ~tp;
    tp
  | Zero -> D.Nat
  | Suc term -> check ~env ~term ~tp:Nat; D.Nat
  | Fst p ->
    begin
      match synth ~env ~term:p with
      | Sg (left_tp, _) -> left_tp
      | t -> tp_error (Misc ("Expecting Sg but found\n" ^ D.show t))
    end
  | Snd p ->
    begin
      match synth ~env ~term:p with
      | Sg (_, right_tp) ->
        let proj = E.eval (Fst p) (Q.env_to_sem_env env) in
        E.do_clos (Q.get_range env) right_tp proj
      | t -> tp_error (Misc ("Expecting Sg but found\n" ^ D.show t))
    end
  | Ap (f, a) ->
    begin
      match synth ~env ~term:f with
      | Pi (src, dest) ->
        check ~env ~term:a ~tp:src;
        let a_sem = E.eval a (Q.env_to_sem_env env) in
        E.do_clos (Q.get_range env) dest a_sem
      | t -> tp_error (Misc ("Expecting Pi but found\n" ^ D.show t))
    end
  | NRec (mot, zero, suc, n) ->
    check ~env ~term:n ~tp:Nat;
    let sem_env = Q.env_to_sem_env env in
    let (nat_arg, nat_env) = Q.mk_var Nat env in
    check_tp ~env:nat_env ~term:mot;
    let zero_tp = E.eval mot (D.add_term D.Zero sem_env) in
    check ~env ~term:zero ~tp:zero_tp;
    let ih_tp = E.eval mot (Q.env_to_sem_env nat_env) in
    let (_, ih_env) = Q.mk_var ih_tp nat_env in
    let suc_sem_env = D.resize_env (Q.get_range ih_env) sem_env in
    let suc_tp = E.eval mot (D.add_term (Suc nat_arg) suc_sem_env) in
    check
      ~env:ih_env
      ~term:suc
      ~tp:suc_tp;
    E.eval mot (D.add_term (E.eval n sem_env) sem_env)
  | BApp (term,r) ->
    let sem_r = E.eval_bdim r (Q.env_to_sem_env env) in
    let restricted_env = Q.restrict_env sem_r env in
    begin
      match synth ~env:restricted_env ~term with
      | Bridge clos -> E.do_bclos (Q.get_range env) clos sem_r
      | t -> tp_error (Misc ("Expecting Bridge but found\n" ^ D.show t ^ "\n" ^ Syn.show term ^ "\n" ^ Q.show_env env))
    end
  | J (mot, refl, eq) ->
    begin
      match synth ~env ~term:eq with
      | D.Id (tp', left, right) ->
        let sem_env = Q.env_to_sem_env env in
        let (mot_arg1, mot_env1) = Q.mk_var tp' env in
        let (mot_arg2, mot_env2) = Q.mk_var tp' mot_env1 in
        let (_, mot_env3) = Q.mk_var (D.Id (tp', mot_arg1, mot_arg2)) mot_env2 in
        check_tp ~env:mot_env3 ~term:mot;
        let refl_sem_env = D.resize_env (Q.get_range mot_env1) sem_env in
        let refl_tp = E.eval mot
            (D.add_term (D.Refl mot_arg1) (D.add_term mot_arg1 (D.add_term mot_arg1 refl_sem_env))) in
        check ~env:mot_env1 ~term:refl ~tp:refl_tp;
        E.eval mot (D.add_term (E.eval eq sem_env) (D.add_term right (D.add_term left sem_env)))
      | t -> tp_error (Misc ("Expecting Id but found\n" ^ D.show t))
    end
  | Extent (r, dom, mot, ctx, varcase) ->
    let sem_env = Q.env_to_sem_env env in
    let r' = E.eval_bdim r sem_env in
    let res_env = Q.restrict_env r' env in
    let res_sem_env = Q.env_to_sem_env res_env in
    let (_, dim_env) = Q.mk_bvar res_env in
    check_tp ~env:dim_env ~term:dom;
    let dom' = E.eval dom (Q.env_to_sem_env dim_env) in
    let (_, dom_env) = Q.mk_var dom' dim_env in
    check_tp ~env:dom_env ~term:mot;
    let dom_r = E.eval dom (D.add_bdim r' res_sem_env) in
    check ~env ~term:ctx ~tp:dom_r;
    let dom_bridge = D.Bridge (D.Clos {term = dom; env = res_sem_env}) in
    let (bridge_arg, bridge_env) = Q.mk_var dom_bridge res_env in
    let (varcase_barg, varcase_benv) = Q.mk_bvar bridge_env in
    let varcase_inst = E.do_bapp (Q.get_range varcase_benv) bridge_arg varcase_barg in
    let varcase_mot = E.eval mot
        (D.add_term varcase_inst
           (D.add_bdim varcase_barg
              (D.resize_env (Q.get_range varcase_benv) res_sem_env))) in
    check ~env:varcase_benv ~term:varcase ~tp:varcase_mot;
    E.eval mot
      (D.add_term (E.eval ctx sem_env)
         (D.add_bdim r'
            (D.resize_env (D.get_range sem_env) res_sem_env)))
  | Ungel (mot, term, case) ->
    let (var_arg, var_env) = Q.mk_bvar env in
    begin
      match synth ~env:var_env ~term with
      | D.Gel (i, tp) ->
        assert_bdim_equal (D.BVar i) var_arg;
        let syn_tp = Q.read_back_tp env tp in
        let sem_env = Q.env_to_sem_env env in
        let mot_hyp =
          D.Bridge (D.Clos {term = Syn.Gel (Syn.BVar 0, syn_tp); env = sem_env}) in
        let (_, hyp_env) = Q.mk_var mot_hyp env in
        check_tp ~env:hyp_env ~term:mot;
        let (_, case_env) = Q.mk_var tp env in
        let gel_term =
          D.BLam
            (D.Clos
               {term = Syn.Engel (Syn.BVar 0, Syn.Var 0);
                env = Q.env_to_sem_env case_env})
        in
        let gel_tp =
          E.eval mot (D.add_term gel_term (D.resize_env (Q.get_range case_env) sem_env)) in
        check ~env:case_env ~term:case ~tp:gel_tp;
        E.eval mot (D.add_term (D.BLam (D.Clos {term; env = sem_env})) sem_env)
      | t -> tp_error (Misc ("Expecting Gel but found\n" ^ D.show t))
    end
  | _ -> tp_error (Cannot_synth_term term)

and check_tp ~env ~term =
  match term with
  | Syn.Nat -> ()
  | Uni _ -> ()
  | Bridge term ->
    let (_, var_env) = Q.mk_bvar env in
    check_tp ~env:var_env ~term
  | Pi (l, r) | Sg (l, r) ->
    check_tp ~env ~term:l;
    let sem_env = Q.env_to_sem_env env in
    let l_sem = E.eval l sem_env in
    let (_, var_env) = Q.mk_var l_sem env in
    check_tp ~env:var_env ~term:r
  | Let (def, body) ->
    let def_tp = synth ~env ~term:def in
    let def_val = E.eval def (Q.env_to_sem_env env) in
    let def_env = Q.add_def ~term:def_val ~tp:def_tp env in
    check_tp ~env:def_env ~term:body
  | Id (tp, l, r) ->
    check_tp ~env ~term:tp;
    let tp = E.eval tp (Q.env_to_sem_env env) in
    check ~env ~term:l ~tp;
    check ~env ~term:r ~tp
  | Gel (r, tp) ->
    let r' = E.eval_bdim r (Q.env_to_sem_env env) in
    check_tp ~env:(Q.restrict_env r' env) ~term:tp
  | term ->
    begin
      match synth ~env ~term with
      | D.Uni _ -> ()
      | t -> tp_error (Expecting_universe t)
    end
