(* This file implements the semantic type-checking algorithm described in the paper. *)
module D = Domain
module Syn = Syntax
module E = Eval
module Q = Quote

type env_entry =
  | BVar of int
  | Var of {level : int; tp : Domain.t}
  | Def of {term : Domain.t; tp : Domain.t}
  | Restrict of int
[@@deriving show, eq]
type env = env_entry list
[@@deriving show, eq]

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

let rec env_to_sem_env = function
  | [] -> []
  | BVar i :: env -> D.BDim (D.BVar i) :: env_to_sem_env env
  | Var {level; tp} :: env -> D.Term (D.Neutral {tp; term = D.Root level}) :: env_to_sem_env env
  | Def {term; _} :: env -> D.Term term :: env_to_sem_env env
  | Restrict _ :: env -> env_to_sem_env env

let rec env_to_quote_env = function
  | [] -> []
  | BVar i :: env -> Q.BVar i :: env_to_quote_env env
  | Var {level; tp} :: env -> Q.Var {level; tp} :: env_to_quote_env env
  | Def {term; _} :: env -> Q.Def term :: env_to_quote_env env
  | Restrict _ :: env -> env_to_quote_env env

let read_back_level env x =
  let rec go acc = function
    | BVar i :: env -> if i = x then acc else go (acc + 1) env
    | Var {level; _} :: env -> if level = x then acc else go (acc + 1) env
    | Def _ :: env -> go (acc + 1) env
    | Restrict _ :: env -> go acc env
    | [] -> tp_error (Misc "read back non-existent variable\n")
  in
  go 0 env

let rec get_tp env x =
  match x, env with
  | _, [] -> tp_error (Misc "Tried to access non-existent variable\n")
  | x, Restrict j :: env ->
    if x < j
    then tp_error (Misc "Tried to use restricted term variable\n")
    else get_tp env x
  | 0, Var {tp; _} :: _ -> tp
  | 0, Def {tp; _} :: _ -> tp
  | 0, BVar j :: _ -> tp_error (Expecting_term j)
  | x, _ :: env -> get_tp env (x - 1)

let mk_bvar env size =
  (D.BVar size, BVar size :: env)

let mk_var tp env size =
  (D.Neutral {tp; term = Root size}, Var {level = size; tp} :: env)

let restrict_env r env =
  match r with
  | Syn.BVar i -> Restrict i :: env

let assert_subtype env size t1 t2 =
  if Q.check_tp ~subtype:true env size t1 t2
  then ()
  else tp_error (Type_mismatch (t1, t2))

let assert_equal env size t1 t2 tp =
  if Q.check_nf env size (D.Normal {tp; term = t1}) (D.Normal {tp; term = t2})
  then ()
  else tp_error (Type_mismatch (t1, t2))

let assert_bdim_equal b1 b2 =
  if b1 = b2 then ()
  else tp_error (BDim_mismatch (b1, b2))

let check_bdim ~env ~bdim =
  let rec go i env =
    match i, env with
    | _, [] -> tp_error (Misc "Tried to access non-existent variable\n")
    | i, Restrict j :: env ->
      if i = j
      then tp_error (Misc "Tried to use restricted dimension\n")
      else go i env
    | 0, BVar _ :: _ -> ()
    | 0, _ :: _ -> tp_error (Misc "Expected bridge dimension\n")
    | i, _ :: env -> go (i - 1) env
  in
  match bdim with
  | Syn.BVar i -> go i env

let rec check ~env ~size ~term ~tp =
  match term with
  | Syn.Let (def, body) ->
    let def_tp = synth ~env ~size ~term:def in
    let def_val = E.eval def (env_to_sem_env env) size in
    check ~env:(Def {term = def_val; tp = def_tp} :: env) ~size ~term:body ~tp
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
        let dest_tp = E.do_clos (size + 1) clos arg in
        check ~env:arg_env ~size:(size + 1) ~term:body ~tp:dest_tp;
      | t -> tp_error (Misc ("Expecting Pi but found\n" ^ D.show t))
    end
  | Pair (left, right) ->
    begin
      match tp with
      | D.Sg (left_tp, right_tp) ->
        check ~env ~size ~term:left ~tp:left_tp;
        let left_sem = E.eval left (env_to_sem_env env) size in
        check ~env ~size ~term:right ~tp:(E.do_clos size right_tp left_sem)
      | t -> tp_error (Misc ("Expecting Sg but found\n" ^ D.show t))
    end
  | Bridge term ->
    begin
      match tp with
      | Uni _ ->
        let (_, arg_env) = mk_bvar env size in
        check ~env:arg_env ~size:(size + 1) ~term ~tp
      | t -> tp_error (Expecting_universe t)
    end
  | BLam body ->
    begin
      match tp with
      | Bridge clos ->
        let (arg, arg_env) = mk_bvar env size in
        let dest_tp = E.do_bclos (size + 1) clos arg in
        check ~env:arg_env ~size:(size + 1) ~term:body ~tp:dest_tp
      | t -> tp_error (Misc ("Expecting Bridge but found\n" ^ D.show t))
    end
  | Gel (r, term) ->
    check_bdim ~env ~bdim:r;
    begin
      match tp with
      | Uni _ ->
        check ~env:(restrict_env r env) ~size ~term ~tp;
      | t -> tp_error (Expecting_universe t)
    end
  | Engel (r, term) ->
    check_bdim ~env ~bdim:r;
    begin
      match r with
      | BVar i ->
        begin
          match tp with
          | Gel (j, tp) ->
            let sem_env = env_to_sem_env env in
            assert_bdim_equal (E.eval_bdim (Syn.BVar i) sem_env) (D.BVar j);
            check ~env:(restrict_env (Syn.BVar i) env) ~size ~term ~tp
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
  | term -> assert_subtype (env_to_quote_env env) size (synth ~env ~size ~term) tp

and synth ~env ~size ~term =
  match term with
  | Syn.Var i -> get_tp env i
  | Check (term, tp') ->
    let tp = E.eval tp' (env_to_sem_env env) size in
    check ~env ~size ~term ~tp;
    tp
  | Zero -> D.Nat
  | Suc term -> check ~env ~size ~term ~tp:Nat; D.Nat
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
        E.do_clos size right_tp proj
      | t -> tp_error (Misc ("Expecting Sg but found\n" ^ D.show t))
    end
  | Ap (f, a) ->
    begin
      match synth ~env ~size ~term:f with
      | Pi (src, dest) ->
        check ~env ~size ~term:a ~tp:src;
        let a_sem = E.eval a (env_to_sem_env env) size in
        E.do_clos size dest a_sem
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
  | BApp (term,r) ->
    check_bdim ~env ~bdim:r;
    let restricted_env = restrict_env r env in
    begin
      match synth ~env:restricted_env ~size ~term with
      | Bridge clos ->
        let r' = E.eval_bdim r (env_to_sem_env env) in
        E.do_bclos size clos r'
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
  | Extent (r, dom, mot, ctx, varcase) ->
    check_bdim ~env ~bdim:r;
    let sem_env = env_to_sem_env env in
    let r' = E.eval_bdim r sem_env in
    let res_env = restrict_env r env in
    let (_, dim_env) = mk_bvar res_env size in
    check_tp ~env:dim_env ~size:(size + 1) ~term:dom;
    let dom' = E.eval dom (env_to_sem_env dim_env) (size + 1) in
    let (_, dom_env) = mk_var dom' dim_env (size + 1) in
    check_tp ~env:dom_env ~size:(size + 2) ~term:mot;
    let dom_r = E.eval dom (D.BDim r' :: sem_env) size in
    check ~env ~size ~term:ctx ~tp:dom_r;
    let dom_bridge = D.Bridge (D.Clos {term = dom; env = sem_env}) in
    let (bridge_arg, bridge_env) = mk_var dom_bridge res_env size in
    let (varcase_barg, varcase_benv) = mk_bvar bridge_env (size + 1) in
    let varcase_inst = E.do_bapp (size + 2) bridge_arg varcase_barg in
    let varcase_mot =
      E.eval mot (D.Term varcase_inst :: D.BDim varcase_barg :: sem_env) (size + 2) in
    check ~env:varcase_benv ~size:(size + 2) ~term:varcase ~tp:varcase_mot;
    E.eval mot (D.Term (E.eval ctx sem_env size) :: D.BDim r' :: sem_env) size
  | Ungel (mot, term, case) ->
    let (var_arg, var_env) = mk_bvar env size in
    begin
      match synth ~env:var_env ~size:(size + 1) ~term with
      | D.Gel (i, tp) ->
        assert_bdim_equal (D.BVar i) var_arg;
        let (_, dim_env) = mk_bvar env size in
        let syn_tp = Q.read_back_tp (env_to_quote_env dim_env) (size + 1) tp in
        let sem_env = env_to_sem_env env in
        let mot_hyp =
          D.Bridge (D.Clos {term = Syn.Gel (Syn.BVar 0, syn_tp); env = sem_env}) in
        let (_, hyp_env) = mk_var mot_hyp env size in
        check_tp ~env:hyp_env ~size:(size + 1) ~term:mot;
        let (_, case_env) = mk_var tp env size in
        let gel_term =
          D.BLam
            (D.Clos
               {term = Syn.Engel (Syn.BVar 0, Syn.Var 1);
                env = env_to_sem_env case_env})
        in
        let gel_tp = E.eval mot (D.Term gel_term :: sem_env) (size + 1) in
        check ~env:case_env ~size:(size + 1) ~term:case ~tp:gel_tp;
        E.eval mot (D.Term (D.BLam (D.Clos {term; env = sem_env})) :: sem_env) size
      | t -> tp_error (Misc ("Expecting Gel but found\n" ^ D.show t))
    end
  | _ -> tp_error (Cannot_synth_term term)

and check_tp ~env ~size ~term =
  match term with
  | Syn.Nat -> ()
  | Uni _ -> ()
  | Bridge term ->
    let (_, var_env) = mk_bvar env size in
    check_tp ~env:var_env ~size:(size + 1) ~term
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
  | Gel (r, tp) ->
    check_bdim ~env ~bdim:r;
    check_tp ~env:(restrict_env r env) ~size ~term:tp
  | term ->
    begin
      match synth ~env ~size ~term with
      | D.Uni _ -> ()
      | t -> tp_error (Expecting_universe t)
    end
