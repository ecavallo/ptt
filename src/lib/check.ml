(* This file implements the semantic type-checking algorithm described in the paper. *)
module D = Domain
module Syn = Syntax
type env_entry =
  | BDim of D.bdim
  | Term of {term : D.t; tp : D.t}
  | TopLevel of {term : D.t; tp : D.t}
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
  | Misc s -> Format.pp_print_string fmt s

exception Type_error of error

let tp_error e = raise (Type_error e)

let env_to_sem_env =
  List.map
    (function
      | BDim r -> D.BDim r
      | TopLevel {term; _} -> D.Term term
      | Term {term; _} -> D.Term term)

let get_var env n = match List.nth env n with
  | BDim r -> tp_error (Expecting_term r)
  | Term {term = _; tp} -> tp
  | TopLevel {tp; _} -> tp

let assert_subtype size t1 t2 =
  if Nbe.check_tp ~subtype:true size t1 t2
  then ()
  else tp_error (Type_mismatch (t1, t2))

let assert_equal size t1 t2 tp =
  if Nbe.check_nf size (D.Normal {tp; term = t1}) (D.Normal {tp; term = t2})
  then ()
  else tp_error (Type_mismatch (t1, t2))

let rec check ~env ~size ~term ~tp =
  match term with
  | Syn.Let (def, body) ->
    let def_tp = synth ~env ~size ~term:def in
    let def_val = Nbe.eval size def (env_to_sem_env env) in
    check ~env:(add_term ~term:def_val ~tp:def_tp env) ~size:(size + 1) ~term:body ~tp
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
        let tp' = Nbe.eval size tp' (env_to_sem_env env) in
        check ~env ~size ~term:l ~tp:tp';
        check ~env ~size ~term:r ~tp:tp'
      | t -> tp_error (Expecting_universe t)
    end
  | Refl term ->
    begin
      match tp with
      | D.Id (tp, left, right) ->
        check ~env ~size ~term ~tp;
        let term = Nbe.eval size term (env_to_sem_env env) in
        assert_equal size term left tp;
        assert_equal size term right tp
      | t -> tp_error (Misc ("Expecting Id but found\n" ^ D.show t))
    end
  | Pi (l, r) | Sg (l, r) ->
    begin
      match tp with
      | D.Uni _ ->
        check ~env ~size ~term:l ~tp;
        let l_sem = Nbe.eval size l (env_to_sem_env env) in
        let var = D.mk_var l_sem size in
        check ~env:(add_term ~term:var ~tp:l_sem env) ~size ~term:r ~tp
      | t -> tp_error (Expecting_universe t)
    end
  | Lam body ->
    begin
      match tp with
      | D.Pi (arg_tp, clos) ->
        let var = D.mk_var arg_tp size in
        let dest_tp = Nbe.do_clos size clos var in
        check ~env:(add_term ~term:var ~tp:arg_tp env) ~size:(size + 1) ~term:body ~tp:dest_tp;
      | t -> tp_error (Misc ("Expecting Pi but found\n" ^ D.show t))
    end
  | Pair (left, right) ->
    begin
      match tp with
      | D.Sg (left_tp, right_tp) ->
        check ~env ~size ~term:left ~tp:left_tp;
        let left_sem = Nbe.eval size left (env_to_sem_env env) in
        check ~env ~size ~term:right ~tp:(Nbe.do_clos size right_tp left_sem)
      | t -> tp_error (Misc ("Expecting Sg but found\n" ^ D.show t))
    end
  | Box term ->
    begin
      match tp with
      | Uni _ ->
        let var = D.mk_bvar size in
        check ~env:(add_bdim ~bdim:var env) ~size ~term ~tp
      | t -> tp_error (Expecting_universe t)
    end
  | Shut body ->
    begin
      match tp with
      | Box clos ->
        let var = D.mk_bvar size in
        let dest_tp = Nbe.do_bclos size clos var in
        check ~env:(add_bdim ~bdim:var env) ~size:(size + 1) ~term:body ~tp:dest_tp
      | t -> tp_error (Misc ("Expecting Box but found\n" ^ D.show t))
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
  | term -> assert_subtype size (synth ~env ~size ~term) tp

and synth ~env ~size ~term =
  match term with
  | Syn.Var i -> get_var env i
  | Check (term, tp') ->
    let tp = Nbe.eval size tp' (env_to_sem_env env) in
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
        let proj = Nbe.eval size (Fst p) (env_to_sem_env env) in
        Nbe.do_clos size right_tp proj
      | t -> tp_error (Misc ("Expecting Sg but found\n" ^ D.show t))
    end
  | Ap (f, a) ->
    begin
      match synth ~env ~size ~term:f with
      | Pi (src, dest) ->
        check ~env ~size ~term:a ~tp:src;
        let a_sem = Nbe.eval size a (env_to_sem_env env) in
        Nbe.do_clos size dest a_sem
      | t -> tp_error (Misc ("Expecting Pi but found\n" ^ D.show t))
    end
  | NRec (mot, zero, suc, n) ->
    check ~env ~size ~term:n ~tp:Nat;
    let var = D.mk_var Nat size in
    check_tp ~env:(add_term ~term:var ~tp:Nat env) ~size:(size + 1) ~term:mot;
    let sem_env = env_to_sem_env env in
    let zero_tp = Nbe.eval (size + 1) mot (D.Term Zero :: sem_env) in
    let ih_tp = Nbe.eval (size + 1) mot (D.Term var :: sem_env) in
    let ih_var = D.mk_var ih_tp (size + 1) in
    let suc_tp = Nbe.eval (size + 1) mot (D.Term (Suc var) :: sem_env) in
    check ~env ~size ~term:zero ~tp:zero_tp;
    check
      ~env:(add_term ~term:var ~tp:Nat env |> add_term ~term:ih_var ~tp:ih_tp)
      ~size:(size + 2)
      ~term:suc
      ~tp:suc_tp;
    Nbe.eval (size + 1) mot (D.Term (Nbe.eval size n sem_env) :: sem_env)
  | Open (term,r) ->
    (* TODO this is totally broken *)
    let sem_env = env_to_sem_env env in
    let r' = Nbe.eval_bdim r sem_env in
    let new_size =
      match r' with
      | BVar i -> i
    in
    begin
      match synth ~env ~size:new_size ~term with
      | Box clos -> Nbe.do_bclos size clos r'
      | t -> tp_error (Misc ("Expecting Box but found\n" ^ D.show t ^ "\n" ^ Syn.show term ^ "\n" ^ show_env env))
    end
  | J (mot, refl, eq) ->
    let eq_tp = synth ~env ~size ~term:eq in
    begin
      let sem_env = env_to_sem_env env in
      match eq_tp with
      | D.Id (tp', left, right) ->
        let mot_var1 = D.mk_var tp' size in
        let mot_var2 = D.mk_var tp' (size + 1) in
        let mot_var3 = D.mk_var (D.Id (tp', mot_var1, mot_var2)) (size + 1) in
        let mot_env =
          add_term ~term:mot_var1 ~tp:tp' env
          |> add_term ~term:mot_var2 ~tp:tp'
          |> add_term ~term:mot_var3 ~tp:(D.Id (tp', mot_var1, mot_var2)) in
        check_tp ~env:mot_env ~size:(size + 3) ~term:mot;
        let refl_var = D.mk_var tp' size in
        let refl_tp = Nbe.eval (size + 3) mot (D.Term (D.Refl refl_var) :: D.Term refl_var :: D.Term refl_var :: sem_env) in
        check ~env:(add_term ~term:refl_var ~tp:tp' env) ~size:(size + 1) ~term:refl ~tp:refl_tp;
        Nbe.eval (size + 3) mot (D.Term (Nbe.eval size eq sem_env) :: D.Term right :: D.Term left :: sem_env)
      | t -> tp_error (Misc ("Expecting Id but found\n" ^ D.show t))
    end
  | _ -> tp_error (Cannot_synth_term term)

and check_tp ~env ~size ~term =
  match term with
  | Syn.Nat -> ()
  | Uni _ -> ()
  | Box term ->
    let var = D.mk_bvar size in
    check_tp ~env:(add_bdim ~bdim:var env) ~size:(size + 1) ~term
  | Pi (l, r) | Sg (l, r) ->
    check_tp ~env ~size ~term:l;
    let l_sem = Nbe.eval size l (env_to_sem_env env) in
    let var = D.mk_var l_sem size in
    check_tp ~env:(add_term ~term:var ~tp:l_sem env) ~size:(size + 1) ~term:r
  | Let (def, body) ->
    let def_tp = synth ~env ~size ~term:def in
    let def_val = Nbe.eval size def (env_to_sem_env env) in
    check_tp ~env:(add_term ~term:def_val ~tp:def_tp env) ~size:(size + 1) ~term:body
  | Id (tp, l, r) ->
    check_tp ~env ~size ~term:tp;
    let tp = Nbe.eval size tp (env_to_sem_env env) in
    check ~env ~size ~term:l ~tp;
    check ~env ~size ~term:r ~tp
  | term ->
    begin
      match synth ~env ~size ~term with
      | D.Uni _ -> ()
      | t -> tp_error (Expecting_universe t)
    end
