module CS = Concrete_syntax
module S = Syntax
module D = Domain

type env_entry =
  | Dim of string
  | Term of string

type env = Env of {check_env : Check.env; bindings : env_entry list}

let initial_env = Env {check_env = []; bindings = []}

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
    | Dim x :: xs -> if String.equal x key then i else go (i + 1) xs
    | Term x :: xs -> if String.equal x key then i else go (i + 1) xs
  in
  go 0

let rec int_to_term = function
  | 0 -> S.Zero
  | n -> S.Suc (int_to_term (n - 1))

let rec unravel_spine f = function
  | [] -> f
  | x :: xs -> unravel_spine (x f) xs

let rec extent_env env = function
  | [var_bridge; var_dim] -> Dim var_dim :: Term var_bridge :: env
  | name :: names -> extent_env (Term name :: env) names
  | _ -> raise (Check.Type_error (Check.Misc ("Bad length in extent")))

let bind_dim env = function
  | CS.DVar i -> S.DVar (find_idx i env)
  | CS.Const o -> S.Const o

let rec bind env = function
  | CS.Var i -> S.Var (find_idx i env)
  | CS.Let (tp, Binder {name; body}) ->
    S.Let (bind env tp, bind (Term name :: env) body)
  | CS.Check {term; tp} -> S.Check (bind env term, bind env tp)
  | CS.Unit -> S.Unit
  | CS.Triv -> S.Triv
  | CS.Nat -> S.Nat
  | CS.Suc t -> S.Suc (bind env t)
  | CS.Lit i -> int_to_term i
  | CS.NRec
      {mot = Binder {name = mot_name; body = mot_body};
       zero;
       suc = Binder2 {name1 = suc_name1; name2 = suc_name2; body = suc_body};
       nat} ->
    S.NRec
      (bind (Term mot_name :: env) mot_body,
       bind env zero,
       bind (Term suc_name2 :: Term suc_name1 :: env) suc_body,
       bind env nat)
  | CS.Bool -> S.Bool
  | CS.True -> S.True
  | CS.False -> S.False
  | CS.If {mot = Binder {name = mot_name; body = mot_body}; tt; ff; bool} ->
    S.If (bind (Term mot_name :: env) mot_body, bind env tt, bind env ff, bind env bool)
  | CS.Lam (BinderN {names = []; body}) ->
    bind env body
  | CS.Lam (BinderN {names = x :: names; body}) ->
    let lam = CS.Lam (BinderN {names; body}) in
    S.Lam (bind (Term x :: env) lam)
  | CS.Ap (f, args) ->
    unravel_spine (bind env f) (List.map (bind_spine env) args)
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
  | CS.Bridge (Binder {name; body}, endpoints) ->
    S.Bridge (bind (Dim name :: env) body, List.map (bind env) endpoints)
  | CS.BLam (BinderN {names = []; body}) ->
    bind env body
  | CS.BLam (BinderN {names = i :: names; body}) ->
    let blam = CS.BLam (BinderN {names; body}) in
    S.BLam (bind (Dim i :: env) blam)
  | CS.Extent
      {dim;
       dom = Binder {name = dom_dim; body = dom_body};
       mot = Binder2 {name1 = mot_dim; name2 = mot_dom; body = mot_body};
       ctx;
       endcase;
       varcase = BinderN {names; body = var_body}} ->
    S.Extent
      (bind_dim env dim,
       bind (Dim dom_dim :: env) dom_body,
       bind (Term mot_dom :: Dim mot_dim :: env) mot_body,
       bind env ctx,
       List.map (function (CS.Binder {name; body}) -> bind (Term name :: env) body) endcase,
       bind (extent_env env names) var_body)
  | CS.Gel (r, ends, BinderN {names; body}) ->
    S.Gel
      (bind_dim env r,
       List.map (bind env) ends,
       bind (List.rev_append (List.map (fun t -> Term t) names) env) body)
  | CS.Engel (i, ts, t) ->
    S.Engel (find_idx i env, List.map (bind env) ts, bind env t)
  | CS.Ungel
      {width;
       mot = Binder {name = mot_name; body = mot_body};
       gel = Binder {name = gel_name; body = gel_body};
       case = Binder {name = case_name; body = case_body}} ->
    S.Ungel
      (width,
       bind (Term mot_name :: env) mot_body,
       bind (Dim gel_name :: env) gel_body,
       bind (Term case_name :: env) case_body)
  | CS.Uni i -> S.Uni i

and bind_spine env = function
  | CS.Term t -> fun f -> S.Ap (f, bind env t)
  | CS.Dim b -> fun f -> S.BApp (f, bind_dim env b)

let process_decl (Env {check_env; bindings})  = function
  | CS.Def {name; def; tp} ->
    let def = bind bindings def in
    let tp = bind bindings tp in
    Check.check_tp ~env:check_env ~size:0 ~term:tp;
    let sem_env = Check.env_to_sem_env check_env in
    let sem_tp = Eval.eval tp sem_env 0 in
    Check.check ~env:check_env ~size:0 ~term:def ~tp:sem_tp;
    let sem_def = Eval.eval def sem_env 0 in
    let new_env = Check.Def {term = sem_def; tp = sem_tp} :: check_env in
    NoOutput (Env {check_env = new_env; bindings = Term name :: bindings })
  | CS.NormalizeDef name ->
    let err = Check.Type_error (Check.Misc ("Unbound variable: " ^ name)) in
    begin
      let i = find_idx name bindings in
      match List.nth check_env i with
      | Check.Def {term; tp} ->
        NF_def (name, Quote.read_back_nf [] 0 (D.Normal {term; tp}))
      | _ -> raise err
      | exception Failure _ -> raise err
    end
  | CS.NormalizeTerm {term; tp} ->
    let term = bind bindings term in
    let tp = bind bindings tp in
    Check.check_tp ~env:check_env ~size:0 ~term:tp;
    let quote_env = Check.env_to_quote_env check_env in
    let sem_env = Quote.env_to_sem_env quote_env in
    let sem_tp = Eval.eval tp sem_env 0 in
    Check.check ~env:check_env ~size:0 ~term ~tp:sem_tp;
    let sem_term = Eval.eval term sem_env 0 in
    let norm_term = Quote.read_back_nf quote_env 0 (D.Normal {term = sem_term; tp = sem_tp}) in
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
