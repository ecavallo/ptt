(* This file implements the semantic type-checking algorithm described in the paper. *)
module D = Domain
module Syn = Syntax
type env_entry =
  | BDim of D.bdim
  | Term of {term : D.t; tp : D.t}
[@@deriving show]
type env = env_entry list
[@@deriving show]

let add_bdim ~bdim env = BDim bdim :: env
let add_term ~term ~tp env = Term {term; tp} :: env

type error =
    Cannot_synth_term of Syn.t
  | Type_mismatch of D.t * D.t
  | Expecting_universe of D.t
  | Expecting_term of D.bdim
  | Not_fresh of Syn.bdim * Syn.t
  | Misc of string

let pp_error fmt = function
  | Cannot_synth_term t ->
    Format.fprintf fmt "@[<v> Cannot synthesize the type of: @[<hov 2>  ";
    Syn.pp fmt t;
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
  | Expecting_term r ->
    Format.fprintf fmt "@[<v>Expected term but found dimension@ @[<hov 2>";
    D.pp_bdim fmt r;
    Format.fprintf fmt "@]@]@,"
  | Not_fresh (r, t) ->
    Format.fprintf fmt "@[<v>Dimension term@,@[<hov 2>  ";
    Syn.pp_bdim fmt r;
    Format.fprintf fmt "@]@ not fresh in@,@[<hov 2>  ";
    Syn.pp fmt t;
    Format.fprintf fmt "@]@]@,"
  | Misc s -> Format.pp_print_string fmt s

exception Type_error of error

let tp_error e = raise (Type_error e)

let env_to_sem_env =
  List.map
    (function
      | BDim r -> D.BDim r
      | Term {term; _} -> D.Term term)

let get_var env n = match List.nth env n with
  | BDim r -> tp_error (Expecting_term r)
  | Term {term = _; tp} -> tp

let assert_subtype sem_env t1 t2 =
  if Nbe.check_tp ~subtype:true sem_env t1 t2
  then ()
  else tp_error (Type_mismatch (t1, t2))

let assert_equal sem_env t1 t2 tp =
  if Nbe.check_nf sem_env (D.Normal {tp; term = t1}) (D.Normal {tp; term = t2})
  then ()
  else tp_error (Type_mismatch (t1, t2))

let rec check ~env ~term ~tp =
  match term with
  | Syn.Let (def, body) ->
    let def_tp = synth ~env ~term:def in
    let def_val = Nbe.eval def (env_to_sem_env env) in
    check ~env:(add_term ~term:def_val ~tp:def_tp env) ~term:body ~tp
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
        let tp' = Nbe.eval tp' (env_to_sem_env env) in
        check ~env ~term:l ~tp:tp';
        check ~env ~term:r ~tp:tp'
      | t -> tp_error (Expecting_universe t)
    end
  | Refl term ->
    begin
      match tp with
      | D.Id (tp, left, right) ->
        check ~env ~term ~tp;
        let sem_env = env_to_sem_env env in
        let term = Nbe.eval term sem_env in
        assert_equal sem_env term left tp;
        assert_equal sem_env term right tp
      | t -> tp_error (Misc ("Expecting Id but found\n" ^ D.show t))
    end
  | Pi (l, r) | Sg (l, r) ->
    begin
      match tp with
      | D.Uni _ ->
        check ~env ~term:l ~tp;
        let sem_env = env_to_sem_env env in
        let l_sem = Nbe.eval l sem_env in
        let var = D.mk_var l_sem sem_env in
        check ~env:(add_term ~term:var ~tp:l_sem env) ~term:r ~tp
      | t -> tp_error (Expecting_universe t)
    end
  | Lam body ->
    begin
      match tp with
      | D.Pi (arg_tp, clos) ->
        let var = D.mk_var arg_tp (env_to_sem_env env) in
        let dest_tp = Nbe.do_clos clos var in
        check ~env:(add_term ~term:var ~tp:arg_tp env) ~term:body ~tp:dest_tp;
      | t -> tp_error (Misc ("Expecting Pi but found\n" ^ D.show t))
    end
  | Pair (left, right) ->
    begin
      match tp with
      | D.Sg (left_tp, right_tp) ->
        check ~env ~term:left ~tp:left_tp;
        let left_sem = Nbe.eval left (env_to_sem_env env) in
        check ~env ~term:right ~tp:(Nbe.do_clos right_tp left_sem)
      | t -> tp_error (Misc ("Expecting Sg but found\n" ^ D.show t))
    end
  | Bridge term ->
    begin
      match tp with
      | Uni _ ->
        let var = D.mk_bvar (env_to_sem_env env) in
        check ~env:(add_bdim ~bdim:var env) ~term ~tp
      | t -> tp_error (Expecting_universe t)
    end
  | BLam body ->
    begin
      match tp with
      | Bridge clos ->
        let var = D.mk_bvar (env_to_sem_env env) in
        let dest_tp = Nbe.do_bclos clos var in
        check ~env:(add_bdim ~bdim:var env) ~term:body ~tp:dest_tp
      | t -> tp_error (Misc ("Expecting Bridge but found\n" ^ D.show t))
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
  | term -> assert_subtype (env_to_sem_env env) (synth ~env ~term) tp

and synth ~env ~term =
  match term with
  | Syn.Var i -> get_var env i
  | Check (term, tp') ->
    let tp = Nbe.eval tp' (env_to_sem_env env) in
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
        let proj = Nbe.eval (Fst p) (env_to_sem_env env) in
        Nbe.do_clos right_tp proj
      | t -> tp_error (Misc ("Expecting Sg but found\n" ^ D.show t))
    end
  | Ap (f, a) ->
    begin
      match synth ~env ~term:f with
      | Pi (src, dest) ->
        check ~env ~term:a ~tp:src;
        let a_sem = Nbe.eval a (env_to_sem_env env) in
        Nbe.do_clos dest a_sem
      | t -> tp_error (Misc ("Expecting Pi but found\n" ^ D.show t))
    end
  | NRec (mot, zero, suc, n) ->
    check ~env ~term:n ~tp:Nat;
    let sem_env = env_to_sem_env env in
    let var = D.mk_var Nat sem_env in
    check_tp ~env:(add_term ~term:var ~tp:Nat env) ~term:mot;
    let zero_tp = Nbe.eval mot (D.Term Zero :: sem_env) in
    let ih_tp = Nbe.eval mot (D.Term var :: sem_env) in
    let ih_var = D.mk_var ih_tp sem_env in
    let suc_tp = Nbe.eval mot (D.Term (Suc var) :: sem_env) in
    check ~env ~term:zero ~tp:zero_tp;
    check
      ~env:(add_term ~term:var ~tp:Nat env |> add_term ~term:ih_var ~tp:ih_tp)
      ~term:suc
      ~tp:suc_tp;
    Nbe.eval mot (D.Term (Nbe.eval n sem_env) :: sem_env)
  | BApp (term,r) ->
    if not (Syn.dim_is_apart_from ~depth:0 r term) then tp_error (Not_fresh (r,term)) else
    begin
      match synth ~env ~term with
      | Bridge clos ->
        let sem_env = env_to_sem_env env in
        let sem_r = Nbe.eval_bdim r sem_env in
        Nbe.do_bclos clos sem_r
      | t -> tp_error (Misc ("Expecting Bridge but found\n" ^ D.show t ^ "\n" ^ Syn.show term ^ "\n" ^ show_env env))
    end
  | J (mot, refl, eq) ->
    let eq_tp = synth ~env ~term:eq in
    begin
      let sem_env = env_to_sem_env env in
      match eq_tp with
      | D.Id (tp', left, right) ->
        let mot_var1 = D.mk_var tp' sem_env in
        let mot_var2 = D.mk_var tp' (D.Term mot_var1 :: sem_env) in
        let mot_var3 =
          D.mk_var
            (D.Id (tp', mot_var1, mot_var2))
            (D.Term mot_var2 :: D.Term mot_var1 :: sem_env)
        in
        let mot_env =
          add_term ~term:mot_var1 ~tp:tp' env
          |> add_term ~term:mot_var2 ~tp:tp'
          |> add_term ~term:mot_var3 ~tp:(D.Id (tp', mot_var1, mot_var2)) in
        check_tp ~env:mot_env ~term:mot;
        let refl_var = D.mk_var tp' sem_env in
        let refl_tp = Nbe.eval mot (D.Term (D.Refl refl_var) :: D.Term refl_var :: D.Term refl_var :: sem_env) in
        check ~env:(add_term ~term:refl_var ~tp:tp' env) ~term:refl ~tp:refl_tp;
        Nbe.eval mot (D.Term (Nbe.eval eq sem_env) :: D.Term right :: D.Term left :: sem_env)
      | t -> tp_error (Misc ("Expecting Id but found\n" ^ D.show t))
    end
  | Extent (r, dom, mot, ctx, varcase) ->
    if not (Syn.dim_is_apart_from ~depth:1 r dom) then tp_error (Not_fresh (Syn.lift_bdim 1 r, dom)) else
    if not (Syn.dim_is_apart_from ~depth:2 r mot) then tp_error (Not_fresh (Syn.lift_bdim 2 r, mot)) else
    if not (Syn.dim_is_apart_from ~depth:2 r varcase) then tp_error (Not_fresh (Syn.lift_bdim 2 r,varcase)) else
    let sem_env = env_to_sem_env env in
    let dim_var = D.mk_bvar sem_env in
    let dim_env = add_bdim ~bdim:dim_var env in
    check_tp ~env:dim_env ~term:dom;
    let sem_dom = Nbe.eval dom (D.BDim dim_var :: sem_env) in
    let dom_var = D.mk_var sem_dom (D.BDim dim_var :: sem_env) in
    check_tp ~env:(add_term ~term:dom_var ~tp:sem_dom dim_env) ~term:mot;
    let sem_r = Nbe.eval_bdim r sem_env in
    let r_dom = Nbe.eval dom (D.BDim sem_r :: sem_env) in
    check ~env ~term:ctx ~tp:r_dom;
    let dom_bridge = D.Bridge (D.Clos {term = dom; env = sem_env}) in
    let varcase_bridge = D.mk_var dom_bridge sem_env in
    let varcase_dim = D.mk_bvar (D.Term varcase_bridge :: sem_env) in
    let varcase_inst = Nbe.do_bapp varcase_bridge varcase_dim in
    let varcase_mot = Nbe.eval mot (D.Term varcase_inst :: D.BDim varcase_dim :: sem_env) in
    let varcase_env =
      add_term ~term:varcase_bridge ~tp:dom_bridge env |> add_bdim ~bdim:varcase_dim in
    check ~env:varcase_env ~term:varcase ~tp:varcase_mot;
    Nbe.eval mot (D.Term (Nbe.eval ctx sem_env) :: D.BDim sem_r :: sem_env)
  | _ -> tp_error (Cannot_synth_term term)

and check_tp ~env ~term =
  match term with
  | Syn.Nat -> ()
  | Uni _ -> ()
  | Bridge term ->
    let var = D.mk_bvar (env_to_sem_env env) in
    check_tp ~env:(add_bdim ~bdim:var env) ~term
  | Pi (l, r) | Sg (l, r) ->
    check_tp ~env ~term:l;
    let sem_env = env_to_sem_env env in
    let l_sem = Nbe.eval l sem_env in
    let var = D.mk_var l_sem sem_env in
    check_tp ~env:(add_term ~term:var ~tp:l_sem env) ~term:r
  | Let (def, body) ->
    let def_tp = synth ~env ~term:def in
    let def_val = Nbe.eval def (env_to_sem_env env) in
    check_tp ~env:(add_term ~term:def_val ~tp:def_tp env) ~term:body
  | Id (tp, l, r) ->
    check_tp ~env ~term:tp;
    let tp = Nbe.eval tp (env_to_sem_env env) in
    check ~env ~term:l ~tp;
    check ~env ~term:r ~tp
  | term ->
    begin
      match synth ~env ~term with
      | D.Uni _ -> ()
      | t -> tp_error (Expecting_universe t)
    end
