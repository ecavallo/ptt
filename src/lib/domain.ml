type bdim =
  (* | BZero
   * | BOne *)
  | BVar of int
[@@deriving show, eq]

type env_entry =
  | BDim of bdim
  | Term of t
and env = env_entry list
[@@deriving show, eq]
and clos =
    Clos of {term : Syntax.t; env : env}
  | ConstClos of t
[@@deriving show, eq]
and clos2 = Clos2 of {term : Syntax.t; env : env}
[@@deriving show, eq]
and clos3 = Clos3 of {term : Syntax.t; env : env}
[@@deriving show, eq]
and abs = Abs of {var : int; ne : ne}
[@@deriving show, eq]
and t =
  | Lam of clos
  | Neutral of {tp : t; term : ne}
  | Nat
  | Zero
  | Suc of t
  | Pi of t * clos
  | Sg of t * clos
  | Pair of t * t
  | Bridge of clos
  | BLam of clos
  | Refl of t
  | Id of t * t * t
  | Gel of int * t
  | Engel of int * t
  | Uni of Syntax.uni_level
[@@deriving show, eq]
and ne =
  | Var of int (* DeBruijn levels for variables *)
  | Ap of ne * nf
  | Fst of ne
  | Snd of ne
  | BApp of ne * int
  | NRec of clos * t * clos2 * ne
  | J of clos3 * clos * t * t * t * ne
  | Extent of int * clos * clos2 * t * clos2
  | Ungel of abs
[@@deriving show, eq]
and nf =
  | Normal of {tp : t; term : t}
                [@@deriving show, eq]

let mk_bvar env = BVar (List.length env)

let mk_var tp env = Neutral {tp; term = Var (List.length env)}

(* TODO document preconditions *)

let subst_bvar_bvar r i j =
  if j = i then r else
  if j > i then j - 1
  else j

let subst_bvar_bdim r i = function
  | BVar j -> BVar (subst_bvar_bvar r i j)

let rec subst_bvar_entry r i = function
  | BDim s -> BDim (subst_bvar_bdim r i s)
  | Term t -> Term (subst_bvar r i t)

and subst_bvar_clos r i = function
  | Clos {term; env} -> Clos {term; env = List.map (subst_bvar_entry r i) env}
  | ConstClos t -> ConstClos (subst_bvar r i t)
  
and subst_bvar_clos2 r i (Clos2 {term; env = env}) =
  Clos2 {term; env = List.map (subst_bvar_entry r i) env}

and subst_bvar_clos3 r i (Clos3 {term; env = env}) =
  Clos3 {term; env = List.map (subst_bvar_entry r i) env}

and subst_bvar r i = function
  | Lam clo -> Lam (subst_bvar_clos r i clo)
  | Neutral {tp; term} -> Neutral {tp = subst_bvar r i tp; term = subst_bvar_ne r i term}
  | Nat -> Nat
  | Zero -> Zero
  | Suc t -> Suc (subst_bvar r i t)
  | Pi (src, dst) -> Pi (subst_bvar r i src, subst_bvar_clos r i dst)
  | Sg (src, dst) -> Sg (subst_bvar r i src, subst_bvar_clos r i dst)
  | Pair (t, u) -> Pair (subst_bvar r i t, subst_bvar r i u)
  | Bridge dst -> Bridge (subst_bvar_clos r i dst)
  | BLam clo -> BLam (subst_bvar_clos r i clo)
  | Refl t -> Refl (subst_bvar r i t)
  | Id (ty, t, u) -> Id (subst_bvar r i ty, subst_bvar r i t, subst_bvar r i u)
  | Gel (j, t) -> Gel (subst_bvar_bvar r i j, t)
  | Engel (j, t) -> Engel (subst_bvar_bvar r i j, t)
  | Uni i -> Uni i

and subst_bvar_ne r i = function
  | Var j -> Var j
  | Ap (e, t) -> Ap (subst_bvar_ne r i e, subst_bvar_nf r i t)
  | Fst e -> Fst (subst_bvar_ne r i e)
  | Snd e -> Snd (subst_bvar_ne r i e)
  | BApp (e, j) -> BApp (subst_bvar_ne r i e, subst_bvar_bvar r i j)
  | NRec (tp, zero, suc, e) ->
    NRec (subst_bvar_clos r i tp, subst_bvar r i zero, subst_bvar_clos2 r i suc, subst_bvar_ne r i e)
  | J (mot, refl, tp, left, right, e) ->
    J
      (subst_bvar_clos3 r i mot,
       subst_bvar_clos r i refl,
       subst_bvar r i tp,
       subst_bvar r i left,
       subst_bvar r i right,
       subst_bvar_ne r i e)
  | Extent (j, dom, mot, ctx, varcase) ->
    Extent
      (subst_bvar_bvar r i j,
       subst_bvar_clos r i dom,
       subst_bvar_clos2 r i mot,
       subst_bvar r i ctx,
       subst_bvar_clos2 r i varcase)
  | Ungel (Abs {var; ne}) ->
    let i = if i < var then i else i + 1 in
    let r = if r < var then r else r + 1 in
    Ungel (Abs {var; ne = subst_bvar_ne r i ne})

and subst_bvar_nf r i (Normal {tp; term}) =
  Normal {tp = subst_bvar r i tp; term = subst_bvar r i term}
