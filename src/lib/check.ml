(* This file implements the semantic type-checking algorithm described in the paper. *)
module M = Mode
module D = Domain
module Syn = Syntax
module E = Eval
module Q = Quote

type env_entry =
  | DVar of {level : D.lvl; width : int}
  | Var of {level : D.lvl; tp : D.t; modality : M.modality}
  | Def of {term : D.t; tp : D.t}
  | Restrict of Syn.idx
  | Lock of M.modality
  | TopLevel of {mode : M.mode; term : D.t; tp : D.t}
  | Postulate of {mode : M.mode; level : D.lvl; tp : D.t}
[@@deriving show, eq]
type env = env_entry list
[@@deriving show, eq]

type error =
    Cannot_synth_term of Syn.t
  | Mode_mismatch of M.mode * M.mode
  | Dim_mismatch of D.dim * D.dim
  | Type_mismatch of Syn.t * Syn.t
  | Expecting_universe of D.t
  | Expecting_term of D.lvl
  | Expecting_of of string * D.t
  | Misc of string

let pp_error fmt = function
  | Cannot_synth_term t ->
    Format.fprintf fmt "@[<v> Cannot synthesize the type of: @[<hov 2>  ";
    Syn.pp fmt t;
    Format.fprintf fmt "@]@]@,"
  | Mode_mismatch (m1, m2) ->
    Format.fprintf fmt "@[<v>Cannot equate mode@,@[<hov 2>  ";
    M.pp_mode fmt m1;
    Format.fprintf fmt "@]@ with@,@[<hov 2>  ";
    M.pp_mode fmt m2;
    Format.fprintf fmt "@]@]@,"
  | Dim_mismatch (b1, b2) ->
    Format.fprintf fmt "@[<v>Cannot equate dimension@,@[<hov 2>  ";
    D.pp_dim fmt b1;
    Format.fprintf fmt "@]@ with@,@[<hov 2>  ";
    D.pp_dim fmt b2;
    Format.fprintf fmt "@]@]@,"
  | Type_mismatch (t1, t2) ->
    Format.fprintf fmt "@[<v>Cannot equate@,@[<hov 2>  ";
    Syn.pp fmt t2;
    Format.fprintf fmt "@]@ with@,@[<hov 2>  ";
    Syn.pp fmt t1;
    Format.fprintf fmt "@]@]@,"
  | Expecting_universe d ->
    Format.fprintf fmt "@[<v>Expected some universe but found@ @[<hov 2>";
    D.pp fmt d;
    Format.fprintf fmt "@]@]@,"
  | Expecting_term j ->
    Format.fprintf fmt "@[<v>Expected term variable but found dimension@ @[<hov 2>";
    Format.pp_print_int fmt j;
    Format.fprintf fmt "@]@]@,"
  | Expecting_of (s, t) ->
    Format.fprintf fmt "@[<v>Expecting@,@[<hov 2>  ";
    Format.pp_print_string fmt s;
    Format.fprintf fmt "@]@ but found@,@[<hov 2>  ";
    D.pp fmt t;
    Format.fprintf fmt "@]@]@,"
  | Misc s -> Format.pp_print_string fmt s

exception Type_error of error

let tp_error e = raise (Type_error e)

let rec env_to_sem_env = function
  | [] -> []
  | DVar {level; _} :: env -> D.Dim (D.DVar level) :: env_to_sem_env env
  | Var {level; tp} :: env -> D.Tm (D.Neutral {tp; term = D.root (D.Var level)}) :: env_to_sem_env env
  | Def {term; _} :: env -> D.Tm term :: env_to_sem_env env
  | Restrict _ :: env -> env_to_sem_env env
  | Lock _ :: env -> env_to_sem_env env
  | TopLevel {term; _} :: env -> D.TopLevel term :: env_to_sem_env env
  | Postulate {level; tp; _} :: env ->
    D.TopLevel (D.Neutral {tp; term = D.root (D.Var level)}) :: env_to_sem_env env

let rec env_to_quote_env = function
  | [] -> []
  | DVar {level; _} :: env -> Q.DVar level :: env_to_quote_env env
  | Var {level; tp} :: env -> Q.Var {level; tp} :: env_to_quote_env env
  | Def {term; _} :: env -> Q.Def term :: env_to_quote_env env
  | Restrict _ :: env -> env_to_quote_env env
  | Lock _ :: env -> env_to_quote_env env
  | TopLevel {term; _} :: env -> Q.TopLevel term :: env_to_quote_env env
  | Postulate {level; tp; _} :: env -> Q.Postulate {level; tp} :: env_to_quote_env env

let assert_mode_equal m1 m2 =
  if m1 = m2 then ()
  else tp_error (Mode_mismatch (m1, m2))

let modality_dst mode m =
  try M.dst mode m
  with M.Mode_mismatch _ -> tp_error (Misc ("Modality " ^ M.show_modality m ^ " does not have source " ^ M.show_mode mode ^ "\n"))

let assert_modality_leq m1 m2 =
  if M.leq m1 m2
  then ()
  else tp_error (Misc ("Tried to use variable behind modality: " ^ M.show_modality m1 ^ " ≰ " ^ M.show_modality m2 ^ "\n"))

let synth_var ~mode env x =
  let rec go synth_mod env x =
    match x, env with
    | _, [] -> tp_error (Misc "Tried to access non-existent variable\n")
    | x, Restrict j :: env ->
      if x < j
      then tp_error (Misc "Tried to use restricted term variable\n")
      else go synth_mod env x
    | x, Lock m :: env -> go (M.compose synth_mod m) env x
    | 0, Var {tp; modality; _} :: _ ->
      assert_modality_leq synth_mod modality; tp
    | 0, Def {tp; _} :: _ ->
      assert_modality_leq synth_mod M.Id; tp
    | 0, DVar {level; _} :: _ -> tp_error (Expecting_term level)
    | 0, TopLevel {mode = m; tp; _} :: _ ->
      assert_mode_equal mode m; tp
    | 0, Postulate {mode = m; tp; _} :: _ ->
      assert_mode_equal mode m; tp
    | x, _ :: env -> go synth_mod env (x - 1)
  in
  go M.Id env x

let mk_bvar width env size =
  (D.DVar size, DVar {level = size; width} :: env)

let mk_modal_var modality tp env size =
  (D.Neutral {tp; term = D.root (D.Var size)}, Var {level = size; tp; modality = modality} :: env)

let mk_var tp env size =
  mk_modal_var M.Id tp env size

let mk_vars tps env size =
  (List.mapi (fun i tp -> D.Neutral {tp; term = D.root (D.Var (size + i))}) tps,
   List.rev_append
     (List.mapi (fun i tp -> Var {level = size + i; tp; modality = M.Id}) tps)
     env)

let restrict_env r env =
  match r with
  | Syn.DVar i -> Restrict i :: env
  | Syn.Const _ -> env

let assert_subtype env size t1 t2 =
  if Q.check_tp ~subtype:true env size t1 t2
  then ()
  else tp_error (Type_mismatch (Q.read_back_tp env size t1, Q.read_back_tp env size t2))

let assert_equal env size t1 t2 tp =
  if Q.check_nf env size (D.Normal {tp; term = t1}) (D.Normal {tp; term = t2})
  then ()
  else tp_error (Type_mismatch (Q.read_back_tp env size t1, Q.read_back_tp env size t2))

let assert_dim_equal b1 b2 =
  if b1 = b2 then ()
  else tp_error (Dim_mismatch (b1, b2))

let check_dim ~mode ~env ~dim ~width =
  let rec go check_mod i env =
    match i, env with
    | _, [] -> tp_error (Misc "Tried to access non-existent variable\n")
    | i, Restrict j :: env ->
      if i = j
      then tp_error (Misc "Tried to use restricted dimension\n")
      else go check_mod i env
    | i, Lock m :: env ->
      go (M.compose check_mod m) i env
    | 0, DVar {width = w; _} :: _ ->
      assert_modality_leq check_mod M.Id;
      if width = w
      then ()
      else tp_error (Misc "Dimension width mismatch\n")
    | 0, _ :: _ -> tp_error (Misc "Expected bridge dimension\n")
    | i, _ :: env -> go check_mod (i - 1) env
  in
  assert_mode_equal mode M.Parametric;
  match dim with
  | Syn.DVar i ->
    go M.Id i env
  | Syn.Const o ->
    if o < width
    then ()
    else tp_error (Misc "Dimension constant out of bounds\n")

let rec check ~mode ~env ~size ~term ~tp =
  match tp with
  | D.Neutral {term = (D.Ext e, tp_spine); _} ->
    begin
      match Q.reduce_extent (env_to_quote_env env) size (e, tp_spine) with
      | Some tp -> check ~mode ~env ~size ~term ~tp
      | None -> check_inert ~mode ~env ~size ~term ~tp
    end
  | _ -> check_inert ~mode ~env ~size ~term ~tp

and check_inert ~mode ~env ~size ~term ~tp =
  match term with
  | Syn.Let (def, body) ->
    let def_tp = synth ~mode ~env ~size ~term:def in
    let def_val = E.eval def (env_to_sem_env env) size in
    check ~mode ~env:(Def {term = def_val; tp = def_tp} :: env) ~size ~term:body ~tp
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
  | List term ->
    begin
      match tp with
      | D.Uni _ -> check ~mode ~env ~size ~term ~tp
      | t -> tp_error (Expecting_universe t)
    end
  | Nil ->
    begin
      match tp with
      | D.List _ -> ()
      | t -> tp_error (Expecting_of ("List", t))
    end
  | Cons (a, t) ->
    begin
      match tp with
      | D.List tp ->
        check ~mode ~env ~size ~term:a ~tp;
        check ~mode ~env ~size ~term:t ~tp:(D.List tp)
      | t -> tp_error (Expecting_of ("List", t))
    end
  | Bool ->
    begin
      match tp with
      | D.Uni _ -> ()
      | t -> tp_error (Expecting_universe t)
    end
  | Coprod (left, right) ->
    begin
      match tp with
      | D.Uni _ ->
        check ~mode ~env ~size ~term:left ~tp;
        check ~mode ~env ~size ~term:right ~tp
      | t -> tp_error (Expecting_universe t)
    end
  | Inl a ->
    begin
      match tp with
      | D.Coprod (left, _) -> check ~mode ~env ~size ~term:a ~tp:left
      | t -> tp_error (Expecting_of ("Coprod", t))
    end
  | Inr b ->
    begin
      match tp with
      | D.Coprod (_, right) -> check ~mode ~env ~size ~term:b ~tp:right
      | t -> tp_error (Expecting_of ("Coprod", t))
    end
  | Void ->
    begin
      match tp with
      | D.Uni _ -> ()
      | t -> tp_error (Expecting_universe t)
    end
  | Id (tp', l, r) ->
    begin
      match tp with
      | D.Uni _ ->
        check ~mode ~env ~size ~term:tp' ~tp;
        let tp' = E.eval tp' (env_to_sem_env env) size in
        check ~mode ~env ~size ~term:l ~tp:tp';
        check ~mode ~env ~size ~term:r ~tp:tp'
      | t -> tp_error (Expecting_universe t)
    end
  | Refl term ->
    begin
      match tp with
      | D.Id (tp, left, right) ->
        check ~mode ~env ~size ~term ~tp;
        let quote_env = env_to_quote_env env in
        let sem_env = Q.env_to_sem_env quote_env in
        let term = E.eval term sem_env size in
        assert_equal quote_env size term left tp;
        assert_equal quote_env size term right tp
      | t -> tp_error (Expecting_of ("Id", t))
    end
  | Pi (m, l, r) ->
    begin
      match tp with
      | D.Uni _ ->
        check ~mode:(modality_dst mode m) ~env:(Lock m :: env) ~size ~term:l ~tp;
        let l_sem = E.eval l (env_to_sem_env env) size in
        let (_, arg_env) = mk_modal_var m l_sem env size in
        check ~mode ~env:arg_env ~size:(size + 1) ~term:r ~tp
      | t -> tp_error (Expecting_universe t)
    end
  | Lam body ->
    begin
      match tp with
      | D.Pi (m, arg_tp, clos) ->
        let (arg, arg_env) = mk_modal_var m arg_tp env size in
        let dest_tp = E.do_clos (size + 1) clos (D.Tm arg) in
        check ~mode ~env:arg_env ~size:(size + 1) ~term:body ~tp:dest_tp;
      | t -> tp_error (Expecting_of ("Pi", t))
    end
  | Sg (l, r) ->
    begin
      match tp with
      | D.Uni _ ->
        check ~mode ~env ~size ~term:l ~tp;
        let l_sem = E.eval l (env_to_sem_env env) size in
        let (_, arg_env) = mk_var l_sem env size in
        check ~mode ~env:arg_env ~size:(size + 1) ~term:r ~tp
      | t -> tp_error (Expecting_universe t)
    end
  | Pair (left, right) ->
    begin
      match tp with
      | D.Sg (left_tp, right_tp) ->
        check ~mode ~env ~size ~term:left ~tp:left_tp;
        let left_sem = E.eval left (env_to_sem_env env) size in
        check ~mode ~env ~size ~term:right ~tp:(E.do_clos size right_tp (D.Tm left_sem))
      | t -> tp_error (Expecting_of ("Sigma", t))
    end
  | Bridge (term, ends) ->
    assert_mode_equal mode Parametric;
    begin
      match tp with
      | Uni _ ->
        let width = List.length ends in
        let (_, arg_env) = mk_bvar width env size in
        check ~mode ~env:arg_env ~size:(size + 1) ~term ~tp;
        let width = List.length ends in
        let tps = E.do_consts size (D.Clos {term; env = env_to_sem_env env}) width in
        List.iter2 (fun tp -> Option.fold () (fun term -> check ~mode ~env ~size ~term ~tp)) tps ends
      | t -> tp_error (Expecting_universe t)
    end
  | BLam body ->
    assert_mode_equal mode Parametric;
    begin
      match tp with
      | Bridge (clos, ends) ->
        let width = List.length ends in
        let (arg, arg_env) = mk_bvar width env size in
        let dest_tp = E.do_clos (size + 1) clos (D.Dim arg) in
        check ~mode ~env:arg_env ~size:(size + 1) ~term:body ~tp:dest_tp;
        let quote_env = env_to_quote_env env in
        let sem_env = Q.env_to_sem_env quote_env in
        List.iteri
          (fun o ->
             Option.fold ()
               (fun pt ->
                  let body_o = E.eval body (D.Dim (D.Const o) :: sem_env) size in
                  let tp = E.do_clos size clos (D.Dim (D.Const o)) in
                  assert_equal quote_env size body_o pt tp))
          ends
      | t -> tp_error (Expecting_of ("Bridge", t))
    end
  | Gel (r, ends, rel) ->
    assert_mode_equal mode Parametric;
    begin
      match tp with
      | Uni _ ->
        let width = List.length ends in
        check_dim ~mode ~env ~dim:r ~width;
        let res_env = restrict_env r env in
        List.iter (fun term -> check ~mode ~env:res_env ~size ~term ~tp) ends;
        let sem_env = env_to_sem_env res_env in
        let ends' = List.map (fun t -> E.eval t sem_env size) ends in
        let (_, rel_env) = mk_vars ends' res_env size in
        check ~mode ~env:rel_env ~size:(size + width) ~term:rel ~tp;
      | t -> tp_error (Expecting_universe t)
    end
  | Engel (i, ts, term) ->
    assert_mode_equal mode Parametric;
    begin
      match tp with
      | Gel (j, ends, rel) ->
        let r = Syn.DVar i in
        let width = List.length ts in
        check_dim ~mode ~env ~dim:r ~width;
        let sem_env = env_to_sem_env env in
        assert_dim_equal (E.eval_dim r sem_env) (D.DVar j);
        let res_env = restrict_env r env in
        List.iter2 (fun term tp -> check ~mode ~env:res_env ~size ~term ~tp) ts ends;
        let ts' = List.map (fun t -> E.eval t sem_env size) ts in
        check ~mode ~env:res_env ~size ~term ~tp:(E.do_closN size rel ts')
      | t -> tp_error (Misc ("Expecting Gel but found\n" ^ D.show t))
    end
  | Codisc term ->
    assert_mode_equal mode Parametric;
    begin
      match tp with
      | D.Uni _ ->
        check ~mode:Pointwise ~env:(Lock M.Global :: env) ~size ~term ~tp;
      | t -> tp_error (Expecting_universe t)
    end
  | Encodisc term ->
    assert_mode_equal mode Parametric;
    begin
      match tp with
      | D.Codisc tp ->
        check ~mode:Pointwise ~env:(Lock M.Global :: env) ~size ~term ~tp;
      | t -> tp_error (Expecting_of ("Codisc", t))
    end
  | Global term ->
    assert_mode_equal mode Pointwise;
    begin
      match tp with
      | D.Uni _ ->
        check ~mode:Parametric ~env:(Lock M.Discrete :: env) ~size ~term ~tp;
      | t -> tp_error (Expecting_universe t)
    end
  | Englobe term ->
    assert_mode_equal mode Pointwise;
    begin
      match tp with
      | D.Global tp ->
        check ~mode:Parametric ~env:(Lock M.Discrete :: env) ~size ~term ~tp;
      | t -> tp_error (Expecting_of ("Global", t))
    end
  | Disc term ->
    assert_mode_equal mode Parametric;
    begin
      match tp with
      | D.Uni _ ->
        check ~mode:Pointwise ~env:(Lock M.Components :: env) ~size ~term ~tp;
      | t -> tp_error (Expecting_universe t)
    end
  | Endisc term ->
    assert_mode_equal mode Parametric;
    begin
      match tp with
      | D.Disc tp ->
        check ~mode:Pointwise ~env:(Lock M.Components :: env) ~size ~term ~tp;
      | t -> tp_error (Expecting_universe t)
    end
  | Uni i ->
    begin
      match tp with
      | Uni j when i < j -> ()
      | t ->
        let msg =
          "Expecting universe over " ^ string_of_int i ^ " but found\n" ^ D.show t ^ "\n" in
        tp_error (Misc msg)
    end
  | term -> assert_subtype (env_to_quote_env env) size (synth ~mode ~env ~size ~term) tp

and synth ~mode ~env ~size ~term =
  let rec go tp =
    match tp with
    | D.Neutral {term = (D.Ext e, tp_spine); _} ->
      begin
        match Q.reduce_extent (env_to_quote_env env) size (e, tp_spine) with
        | Some tp -> go tp
        | None -> tp
      end
    | _ -> tp
  in
  go (synth_quasi ~mode ~env ~size ~term)

and synth_quasi ~mode ~env ~size ~term =
  match term with
  | Syn.Var i -> synth_var ~mode env i
  | Check (term, tp') ->
    let tp = E.eval tp' (env_to_sem_env env) size in
    check ~mode ~env ~size ~term ~tp;
    tp
  | Triv -> D.Unit
  | Zero -> D.Nat
  | Suc term -> check ~mode ~env ~size ~term ~tp:Nat; D.Nat
  | True -> D.Bool
  | False -> D.Bool
  | Fst p ->
    begin
      match synth ~mode ~env ~size ~term:p with
      | Sg (left_tp, _) -> left_tp
      | t -> tp_error (Expecting_of ("Sg", t))
    end
  | Snd p ->
    begin
      match synth ~mode ~env ~size ~term:p with
      | Sg (_, right_tp) ->
        let proj = E.eval (Fst p) (env_to_sem_env env) size in
        E.do_clos size right_tp (D.Tm proj)
      | t -> tp_error (Expecting_of ("Sg", t))
    end
  | Ap (f, a) ->
    begin
      match synth ~mode ~env ~size ~term:f with
      | Pi (m, src, dest) ->
        check ~mode:(modality_dst mode m) ~env:(Lock m :: env) ~size ~term:a ~tp:src;
        let a_sem = E.eval a (env_to_sem_env env) size in
        E.do_clos size dest (D.Tm a_sem)
      | t -> tp_error (Expecting_of ("Pi", t))
    end
  | NRec (mot, zero, suc, n) ->
    check ~mode ~env ~size ~term:n ~tp:Nat;
    let sem_env = env_to_sem_env env in
    let (nat_arg, nat_env) = mk_var Nat env size in
    check_tp ~mode ~env:nat_env ~size:(size + 1) ~term:mot;
    let zero_tp = E.eval mot (D.Tm D.Zero :: sem_env) size in
    check ~mode ~env ~size ~term:zero ~tp:zero_tp;
    let ih_tp = E.eval mot (env_to_sem_env nat_env) (size + 1) in
    let (_, ih_env) = mk_var ih_tp nat_env (size + 1) in
    let suc_tp = E.eval mot (D.Tm (Suc nat_arg) :: sem_env) (size + 2) in
    check ~mode ~env:ih_env ~size:(size + 2) ~term:suc ~tp:suc_tp;
    E.eval mot (D.Tm (E.eval n sem_env size) :: sem_env) size
  | ListRec (mot, nil, cons, l) ->
    begin
      match synth ~mode ~env ~size ~term:l with
      | D.List tp' ->
        let sem_env = env_to_sem_env env in
        let (_, mot_env) = mk_var (D.List tp') env size in
        check_tp ~mode ~env:mot_env ~size:(size + 1) ~term:mot;
        check ~mode ~env ~size ~term:nil ~tp:(E.eval mot (D.Tm D.Nil :: sem_env) size);
        let (cons_arg1, cons_env1) = mk_var tp' env size in
        let (cons_arg2, cons_env2) = mk_var (D.List tp') cons_env1 (size + 1) in
        let rec_mot = E.eval mot (D.Tm cons_arg2 :: sem_env) (size + 2) in
        let (_, cons_env3) = mk_var rec_mot cons_env2 (size + 2) in
        check ~mode ~env:cons_env3 ~size:(size + 3) ~term:cons
          ~tp:(E.eval mot (D.Tm (D.Cons (cons_arg1, cons_arg2)) :: sem_env) (size + 3));
        E.eval mot (D.Tm (E.eval l sem_env size) :: sem_env) size
      | t -> tp_error (Expecting_of ("List", t))
    end
  | If (mot, tt, ff, b) ->
    check ~mode ~env ~size ~term:b ~tp:Bool;
    let sem_env = env_to_sem_env env in
    let (_, bool_env) = mk_var Bool env size in
    check_tp ~mode ~env:bool_env ~size:(size + 1) ~term:mot;
    let tt_tp = E.eval mot (D.Tm D.True :: sem_env) size in
    check ~mode ~env ~size ~term:tt ~tp:tt_tp;
    let ff_tp = E.eval mot (D.Tm D.False :: sem_env) size in
    check ~mode ~env ~size ~term:ff ~tp:ff_tp;
    E.eval mot (D.Tm (E.eval b sem_env size) :: sem_env) size
  | Case (mot, inl, inr, co) ->
    begin
      match synth ~mode ~env ~size ~term:co with
      | D.Coprod (left, right) ->
        let sem_env = env_to_sem_env env in
        let (_, mot_env) = mk_var (D.Coprod (left, right)) env size in
        check_tp ~mode ~env:mot_env ~size:(size + 1) ~term:mot;
        let (inl_arg, inl_env) = mk_var left env size in
        check ~mode ~env:inl_env ~size:(size + 1) ~term:inl
          ~tp:(E.eval mot (D.Tm (D.Inl inl_arg) :: sem_env) (size + 1));
        let (inr_arg, inr_env) = mk_var right env size in
        check ~mode ~env:inr_env ~size:(size + 1) ~term:inr
          ~tp:(E.eval mot (D.Tm (D.Inr inr_arg) :: sem_env) (size + 1));
        E.eval mot (D.Tm (E.eval co sem_env size) :: sem_env) size
      | t -> tp_error (Expecting_of ("Coprod", t))
    end
  | Abort (mot, vd) ->
    check ~mode ~env ~size ~term:vd ~tp:Void;
    let sem_env = env_to_sem_env env in
    let (_, mot_env) = mk_var Void env size in
    check_tp ~mode ~env:mot_env ~size:(size + 1) ~term:mot;
    E.eval mot (D.Tm (E.eval vd sem_env size) :: sem_env) size
  | BApp (term, r) ->
    let restricted_env = restrict_env r env in
    begin
      match synth ~mode ~env:restricted_env ~size ~term with
      | Bridge (clos, ends) ->
        let width = List.length ends in
        check_dim ~mode ~width ~env ~dim:r;
        let r' = E.eval_dim r (env_to_sem_env env) in
        E.do_clos size clos (D.Dim r')
      | t -> tp_error (Expecting_of ("Bridge", t))
    end
  | J (mot, refl, eq) ->
    begin
      match synth ~mode ~env ~size ~term:eq with
      | D.Id (tp', left, right) ->
        let sem_env = env_to_sem_env env in
        let (mot_arg1, mot_env1) = mk_var tp' env size in
        let (mot_arg2, mot_env2) = mk_var tp' mot_env1 (size + 1) in
        let (_, mot_env3) = mk_var (D.Id (tp', mot_arg1, mot_arg2)) mot_env2 (size + 2) in
        check_tp ~mode ~env:mot_env3 ~size:(size + 3) ~term:mot;
        let refl_tp =
          E.eval mot
            (D.Tm (D.Refl mot_arg1) :: D.Tm mot_arg1 :: D.Tm mot_arg1 :: sem_env)
            (size + 1) in
        check ~mode ~env:mot_env1 ~size:(size + 1) ~term:refl ~tp:refl_tp;
        E.eval mot (D.Tm (E.eval eq sem_env size) :: D.Tm right :: D.Tm left :: sem_env) size
      | t -> tp_error (Expecting_of ("Id", t))
    end
  | Extent (r, dom, mot, ctx, endcase, varcase) ->
    assert_mode_equal mode Parametric;
    let width = List.length endcase in
    check_dim ~mode ~env ~dim:r ~width;
    let sem_env = env_to_sem_env env in
    let r' = E.eval_dim r sem_env in
    let res_env = restrict_env r env in
    let (_, dim_env) = mk_bvar width res_env size in
    check_tp ~mode ~env:dim_env ~size:(size + 1) ~term:dom;
    let dom' = E.eval dom (env_to_sem_env dim_env) (size + 1) in
    let (_, dom_env) = mk_var dom' dim_env (size + 1) in
    check_tp ~mode ~env:dom_env ~size:(size + 2) ~term:mot;
    let dom_r = E.eval dom (D.Dim r' :: sem_env) size in
    check ~mode ~env ~size ~term:ctx ~tp:dom_r;
    List.iteri
      (fun o case ->
         let dom_o = E.eval dom (D.Dim (D.Const o) :: sem_env) size in
         let (case_arg, case_env) = mk_var dom_o res_env size in
         let mot_o = E.eval mot (D.Tm case_arg :: D.Dim (D.Const o) :: sem_env) size in
         check ~mode ~env:case_env ~size:(size + 1) ~term:case ~tp:mot_o)
      endcase;
    let end_tps = E.do_consts size (D.Clos {term = dom; env = sem_env}) width in
    let (end_vars, ends_env) = mk_vars end_tps res_env size in
    let dom_bridge = D.Bridge (D.Clos {term = dom; env = sem_env}, List.map Option.some end_vars) in
    let (bridge_arg, bridge_env) = mk_var dom_bridge ends_env (size + width) in
    let (varcase_barg, varcase_benv) = mk_bvar width bridge_env (size + width + 1) in
    let varcase_inst = E.do_bapp (size + width + 2) bridge_arg varcase_barg in
    let varcase_mot =
      E.eval mot (D.Tm varcase_inst :: D.Dim varcase_barg :: sem_env) (size + width + 2) in
    check ~mode ~env:varcase_benv ~size:(size + width + 2) ~term:varcase ~tp:varcase_mot;
    E.eval mot (D.Tm (E.eval ctx sem_env size) :: D.Dim r' :: sem_env) size
  | Ungel (width, mot, term, case) ->
    assert_mode_equal mode Parametric;
    let (var_arg, var_env) = mk_bvar width env size in
    begin
      match synth ~mode ~env:var_env ~size:(size + 1) ~term with
      | D.Gel (i, end_tps, rel) ->
        assert_dim_equal (D.DVar i) var_arg;
        let sem_env = env_to_sem_env env in
        let end_tms = E.do_consts size (D.Clos {term; env = sem_env}) width in
        let mot_hyp =
          D.Bridge
            (D.Pseudo {var = size; term = D.Gel (size, end_tps, rel); ends = end_tps},
             List.map Option.some end_tms) in
        let (_, hyp_env) = mk_var mot_hyp env size in
        check_tp ~mode ~env:hyp_env ~size:(size + 1) ~term:mot;
        let applied_rel = E.do_closN size rel end_tms in
        let (wit_arg, wit_env) = mk_var applied_rel env size in
        let gel_term =
          D.BLam (D.Pseudo {var = size + 1; term = D.Engel (size + 1, end_tms, wit_arg); ends = end_tms}) in
        let gel_tp = E.eval mot (D.Tm gel_term :: sem_env) (size + 1) in
        check ~mode ~env:wit_env ~size:(size + 1) ~term:case ~tp:gel_tp;
        E.eval mot (D.Tm (D.BLam (D.Clos {term; env = sem_env})) :: sem_env) size
      | t -> tp_error (Expecting_of ("Gel", t))
    end
  | Uncodisc term ->
    assert_mode_equal mode Pointwise;
    begin
      match synth ~mode:Parametric ~env:(Lock M.Discrete :: env) ~size ~term with
      | Codisc tp -> tp
      | t -> tp_error (Expecting_of ("Codisc", t))
    end
  | Unglobe term ->
    assert_mode_equal mode Parametric;
    begin
      match synth ~mode:Pointwise ~env:(Lock M.Components :: env) ~size ~term with
      | Global tp -> tp
      | t -> tp_error (Expecting_of ("Global", t))
    end
  | Letdisc (m, mot, case, d) ->
    assert_mode_equal (modality_dst mode m) M.Parametric;
    begin
      match synth ~mode:M.Parametric ~env:(Lock m :: env) ~size ~term:d with
      | Disc tp ->
        let sem_env = env_to_sem_env env in
        let (_, mot_env) = mk_modal_var m (D.Disc tp) env size in
        check_tp ~mode ~env:mot_env ~size:(size + 1) ~term:mot;
        let (case_arg, case_env) = mk_modal_var (M.compose M.Components m) tp env size in
        check ~mode ~env:case_env ~size:(size + 1) ~term:case
          ~tp:(E.eval mot (D.Tm (D.Endisc case_arg) :: sem_env) (size + 1));
        E.eval mot (D.Tm (E.eval d sem_env size) :: sem_env) size
      | t -> tp_error (Expecting_of ("Disc", t))
    end
  | Letdiscbridge (m, width, mot, case, d) ->
    assert_mode_equal (modality_dst mode m) M.Parametric;
    let (_, var_env) = mk_bvar width (Lock m :: env) size in
    begin
      match synth ~mode:M.Parametric ~env:var_env ~size:(size + 1) ~term:d with
      | D.Disc tp ->
        let sem_env = env_to_sem_env env in
        let mot_hyp = D.Bridge (D.ConstClos (D.Disc tp), List.init width (fun _ -> None)) in
        let (_, mot_env) = mk_modal_var m mot_hyp env size in
        check_tp ~mode ~env:mot_env ~size:(size + 1) ~term:mot;
        let (case_arg, case_env) = mk_modal_var (M.compose M.Components m) tp env size in
        check ~mode ~env:case_env ~size:(size + 1) ~term:case
          ~tp:(E.eval mot (D.Tm (D.BLam (D.ConstClos (D.Endisc case_arg))) :: sem_env) (size + 1));
        E.eval mot (D.Tm (D.BLam (D.Clos {term = d; env = sem_env})) :: sem_env) size
      | t -> tp_error (Expecting_of ("Disc", t))
    end
  | _ -> tp_error (Cannot_synth_term term)

and check_tp ~mode ~env ~size ~term =
  match term with
  | Syn.Unit -> ()
  | Syn.Nat -> ()
  | Syn.List term -> check_tp ~mode ~env ~size ~term
  | Syn.Bool -> ()
  | Syn.Coprod (left, right) ->
    check_tp ~mode ~env ~size ~term:left;
    check_tp ~mode ~env ~size ~term:right
  | Syn.Void -> ()
  | Uni _ -> ()
  | Bridge (term, ends) ->
    let width = List.length ends in
    let (_, var_env) = mk_bvar width env size in
    check_tp ~mode ~env:var_env ~size:(size + 1) ~term;
    let sem_env = env_to_sem_env env in
    List.iteri
      (fun o ->
         Option.fold ()
           (fun pt ->
              check ~mode ~env ~size ~term:pt ~tp:(E.eval term (D.Dim (D.Const o) :: sem_env) size)))
      ends
  | Pi (m, l, r) ->
    check_tp ~mode:(modality_dst mode m) ~env:(Lock m :: env) ~size ~term:l;
    let sem_env = env_to_sem_env env in
    let l_sem = E.eval l sem_env size in
    let (_, var_env) = mk_modal_var m l_sem env size in
    check_tp ~mode ~env:var_env ~size:(size + 1) ~term:r
  | Sg (l, r) ->
    check_tp ~mode ~env ~size ~term:l;
    let sem_env = env_to_sem_env env in
    let l_sem = E.eval l sem_env size in
    let (_, var_env) = mk_var l_sem env size in
    check_tp ~mode ~env:var_env ~size:(size + 1) ~term:r
  | Let (def, body) ->
    let def_tp = synth ~mode ~env ~size ~term:def in
    let def_val = E.eval def (env_to_sem_env env) size in
    check_tp ~mode ~env:(Def {term = def_val; tp = def_tp} :: env) ~size ~term:body
  | Id (tp, l, r) ->
    check_tp ~mode ~env ~size ~term:tp;
    let tp = E.eval tp (env_to_sem_env env) size in
    check ~mode ~env ~size ~term:l ~tp;
    check ~mode ~env ~size ~term:r ~tp
  | Gel (r, ends, rel) ->
    let width = List.length ends in
    check_dim ~mode ~env ~dim:r ~width;
    let res_env = restrict_env r env in
    let sem_env = env_to_sem_env res_env in
    List.iter (fun term -> check_tp ~mode ~env:res_env ~size ~term) ends;
    let ends' = List.map (fun term -> E.eval term sem_env size) ends in
    let (_, rel_env) = mk_vars ends' res_env size in
    check_tp ~mode ~env:rel_env ~size:(size + width) ~term:rel
  | Codisc tp ->
    assert_mode_equal mode Parametric;
    check_tp ~mode:Pointwise ~env:(Lock M.Global :: env) ~size ~term:tp
  | Global tp ->
    assert_mode_equal mode Pointwise;
    check_tp ~mode:Parametric ~env:(Lock M.Discrete :: env) ~size ~term:tp
  | Disc tp ->
    assert_mode_equal mode Parametric;
    check_tp ~mode:Pointwise ~env:(Lock M.Components :: env) ~size ~term:tp
  | term ->
    begin
      match synth ~mode ~env ~size ~term with
      | D.Uni _ -> ()
      | t -> tp_error (Expecting_universe t)
    end
