module S = Syntax
module D = Domain

exception Indirect_use
exception Unsubst_failed of string

type hyp = BDim | Term | DeadTerm | New

let env_to_hyps i env =
  let rec go i env =
    match i, env with
    | _, [] -> raise (Unsubst_failed "Tried to unsubst dimension out of scope")
    | 0, _ :: _ -> []
    | i, D.BDim _ :: env -> BDim :: go (i - 1) env
    | i, D.Term _ :: env -> DeadTerm :: go (i - 1) env
  in
  New :: go i env

let find_new hyps =
  let rec go acc = function
    | [] -> raise (Unsubst_failed "Could not find new index")
    | New :: _ -> acc
    | _ :: hyps -> go (acc + 1) hyps
  in
  go 0 hyps

let unsubst_idx i hyps =
  let new_idx = find_new hyps in
  let rec go acc i hyps =
    match i, hyps with
    | 0, [] -> new_idx
    | 0, BDim :: _ -> acc
    | 0, DeadTerm :: _ -> raise Indirect_use
    | 0, Term :: _ -> acc
    | i, [] -> acc + (i - 1)
    | i, BDim :: hyps -> go (acc + 1) (i - 1) hyps
    | i, Term :: hyps -> go (acc + 1) (i - 1) hyps
    | i, DeadTerm :: hyps -> go acc (i - 1) hyps
    | i, New :: hyps -> go (acc + 1) i hyps
  in go 0 i hyps

let rec restrict_bvar j hyps =
  match j, hyps with
  | _, [] -> []
  | n, New :: hyps -> New :: restrict_bvar n hyps
  | 0, _ :: hyps -> hyps
  | n, BDim :: hyps -> BDim :: restrict_bvar (n - 1) hyps
  | n, Term :: hyps -> restrict_bvar (n - 1) hyps
  | n, DeadTerm :: hyps -> restrict_bvar (n - 1) hyps

let restrict r hyps =
  match r with
  | S.BVar j -> restrict_bvar j hyps

let unsubst_bvar i env t =
  let bgo hyps = function
    | S.BVar j -> S.BVar (unsubst_idx j hyps)
  in
  let rec go hyps = function
    | S.Var j -> S.Var (unsubst_idx j hyps)
    | Let (def, body) -> Let (go hyps def, go (Term :: hyps) body)
    | Check (term, tp) -> Check (go hyps term, go hyps tp)
    | Nat -> Nat
    | Zero -> Zero
    | Suc t -> Suc (go hyps t)
    | NRec (mot, zero, suc, n) ->
      NRec (go (Term :: hyps) mot, go hyps zero, go (Term :: Term :: hyps) suc, go hyps n)
    | Pi (l, r) -> Pi (go hyps l, go (Term :: hyps) r)
    | Lam body -> Lam (go (Term :: hyps) body)
    | Ap (l, r) -> Ap (go hyps l, go hyps r)
    | Sg (l, r) -> Sg (go hyps l, go (Term :: hyps) r)
    | Fst body -> Fst (go hyps body)
    | Snd body -> Snd (go hyps body)
    | Pair (l, r) -> Pair (go hyps l, go hyps r)
    | Id (tp, l, r) -> Id (go hyps tp, go hyps l, go hyps r)
    | Refl t -> Refl (go hyps t)
    | J (mot, refl, eq) ->
      J (go (Term :: Term :: Term :: hyps) mot, go (Term :: hyps) refl, go hyps eq)
    | Bridge t -> Bridge (go (BDim :: hyps) t)
    | BLam t -> BLam (go (BDim :: hyps) t)
    | BApp (t, r) -> BApp (go (restrict r hyps) t, bgo hyps r)
    | Extent (r, dom, mot, ctx, varcase) ->
      let restricted_hyps = restrict r hyps in
      Extent
        (bgo hyps r,
         go (BDim :: restricted_hyps) dom,
         go (Term :: BDim :: restricted_hyps) mot,
         go hyps ctx,
         go (BDim :: Term :: restricted_hyps) varcase)
    | Gel (r, t) -> Gel (bgo hyps r, go (restrict r hyps) t)
    | Engel (r, t) -> Engel (bgo hyps r, go (restrict r hyps) t)
    | Ungel (mot, gel, case) ->
      Ungel (go (Term :: hyps) mot, go (BDim :: hyps) gel, go (Term :: hyps) case)
    | Uni j -> Uni j
  in
  try
    Some (go (env_to_hyps i env) t)
  with
    Indirect_use -> None
