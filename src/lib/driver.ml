module CS = Concrete_syntax
module S = Syntax
module D = Domain

type env_entry =
  | BDim of string
  | Term of string

type env = Env of {size : int; check_env : Check.env; bindings : env_entry list}

let initial_env = Env {size = 0; check_env = []; bindings = []}

type output =
  | NoOutput of env
  | NF_term of S.t * S.t
  | NF_def of CS.ident * S.t
  | Quit

let update_env env = function
  | NoOutput env -> env
  | NF_term _ | NF_def _ | Quit -> env

let output = function
  | NoOutput _ -> ()
  | NF_term (s, t) ->
    Format.fprintf Format.std_formatter "Computed normal form of@ @[<hv>";
    S.pp Format.std_formatter s;
    Format.fprintf Format.std_formatter "@] as @ @[<hv>";
    S.pp Format.std_formatter t;
    Format.fprintf Format.std_formatter "@]@,"
  | NF_def (name, t) ->
    Format.fprintf Format.std_formatter "Computed normal form of [%s]:@ @[<hv>" name;
    Syntax.pp Format.std_formatter t;
    Format.fprintf Format.std_formatter "@]@,"
  | Quit -> exit 0

let find_idx key =
  let rec go i = function
    | [] -> raise (Check.Type_error (Check.Misc ("Unbound variable: " ^ key)))
    | BDim x :: xs -> if String.equal x key then i else go (i + 1) xs
    | Term x :: xs -> if String.equal x key then i else go (i + 1) xs
  in
  go 0

let rec int_to_term = function
  | 0 -> S.Zero
  | n -> S.Suc (int_to_term (n - 1))

let rec unravel_spine f = function
  | [] -> f
  | x :: xs -> unravel_spine (x f) xs

let bbind env = function
  | CS.BVar i -> S.BVar (find_idx i env)

let rec bind env = function
  | CS.Var i -> S.Var (find_idx i env)
  | CS.Let (tp, Binder {name; body}) ->
    S.Let (bind env tp, bind (Term name :: env) body)
  | CS.Check {term; tp} -> S.Check (bind env term, bind env tp)
  | CS.Nat -> S.Nat
  | CS.Suc t -> S.Suc (bind env t)
  | CS.Lit i -> int_to_term i
  | CS.NRec
      { mot = Binder {name = mot_name; body = mot_body};
        zero;
        suc = Binder2 {name1 = suc_name1; name2 = suc_name2; body = suc_body};
        nat} ->
    S.NRec
      (bind (Term mot_name :: env) mot_body,
       bind env zero,
       bind (Term suc_name2 :: Term suc_name1 :: env) suc_body,
       bind env nat)
  | CS.Lam (BinderN {names = []; body}) ->
    bind env body
  | CS.Lam (BinderN {names = x :: names; body}) ->
    let lam = CS.Lam (BinderN {names; body}) in
    S.Lam (bind (Term x :: env) lam)
  | CS.Ap (f, args) ->
    List.map (bind_spine env) args |> unravel_spine (bind env f)
  | CS.Sg ([], body) ->
    bind env body
  | CS.Sg (Cell cell :: tele, body) ->
    S.Sg (bind env cell.ty, bind (Term cell.name :: env) (CS.Sg (tele, body)))
  | CS.Pi ([], body) ->
    bind env body
  | CS.Pi (Cell cell :: tele, body) ->
    S.Pi (bind env cell.ty, bind (Term cell.name :: env) (CS.Pi (tele, body)))
  | CS.Pair (l, r) -> S.Pair (bind env l, bind env r)
  | CS.Fst p -> S.Fst (bind env p)
  | CS.Snd p -> S.Snd (bind env p)
  | CS.J
      {mot = Binder3 {name1 = left; name2 = right; name3 = prf; body = mot_body};
       refl = Binder {name = refl_name; body = refl_body};
       eq} ->
    S.J
      (bind (Term prf :: Term right :: Term left :: env) mot_body,
       bind (Term refl_name :: env) refl_body,
       bind env eq)
  | CS.Id (tp, left, right) ->
    S.Id (bind env tp, bind env left, bind env right)
  | CS.Refl t -> S.Refl (bind env t)
  | CS.Box ([], body) ->
    bind env body
  | CS.Box (r :: tele, body) ->
    S.Box (bind (BDim r :: env) (CS.Box (tele, body)))
  | CS.Shut (BBinderN {names = []; body}) ->
    bind env body
  | CS.Shut (BBinderN {names = i :: names; body}) ->
    let shut = CS.Shut (BBinderN {names; body}) in
    S.Shut (bind (BDim i :: env) shut)
  | CS.Open (p, rs) ->
    List.map (bind_bspine env) rs |> unravel_spine (bind env p)
  | CS.Uni i -> S.Uni i

and bind_bspine env r = fun p -> S.Open (p, bbind env r)

and bind_spine env = function
  | CS.Term t -> fun f -> S.Ap (f, bind env t)

let process_decl (Env {size; check_env; bindings})  = function
  | CS.Def {name; def; tp} ->
    let def = bind bindings def in
    let tp = bind bindings tp in
    Check.check_tp ~size ~env:check_env ~term:tp;
    let sem_env = Check.env_to_sem_env check_env in
    let sem_tp = Nbe.eval size tp sem_env in
    Check.check ~size ~env:check_env ~term:def ~tp:sem_tp;
    let sem_def = Nbe.eval size def sem_env in
    let new_entry = Check.TopLevel {term = sem_def; tp = sem_tp} in
    NoOutput (Env {size = size + 1; check_env = new_entry :: check_env; bindings = Term name :: bindings })
  | CS.NormalizeDef name ->
    let err = Check.Type_error (Check.Misc ("Unbound variable: " ^ name)) in
    begin
      match List.nth check_env (find_idx name bindings) with
      | Check.TopLevel {term; tp} -> NF_def (name, Nbe.read_back_nf 0 (D.Normal {term; tp}))
      | _ -> raise err
      | exception Failure _ -> raise err
    end
  | CS.NormalizeTerm {term; tp} ->
    let term = bind bindings term in
    let tp = bind bindings tp in
    Check.check_tp ~size ~env:check_env ~term:tp;
    let sem_env = Check.env_to_sem_env check_env in
    let sem_tp = Nbe.eval size tp sem_env in
    Check.check ~size ~env:check_env ~term ~tp:sem_tp;
    let sem_term = Nbe.eval size term sem_env in
    let norm_term = Nbe.read_back_nf 0 (D.Normal {term = sem_term; tp = sem_tp}) in
    NF_term (term, norm_term)
  | CS.Quit -> Quit

let rec process_sign ?env = function
  | [] -> ()
  | d :: ds ->
    let env = match env with
        None -> initial_env
      | Some e -> e in
    let o = process_decl env d in
    output o;
    process_sign ?env:(Some (update_env env o)) ds

let process_sign : Concrete_syntax.signature -> unit = process_sign
