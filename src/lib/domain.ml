type lvl = int
[@@deriving show{ with_path = false }, eq]

type bdim =
  | BVar of lvl
  | Const of int
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
and closN = ClosN of {term : Syntax.t; env : env}
[@@deriving show, eq]
and t =
  | Lam of clos
  | Neutral of {tp : t; term : ne}
  | Unit
  | Triv
  | Nat
  | Zero
  | Suc of t
  | Bool
  | True
  | False
  | Pi of t * clos
  | Sg of t * clos
  | Pair of t * t
  | Bridge of clos * t list
  | BLam of clos
  | Refl of t
  | Id of t * t * t
  | Gel of lvl * t list * closN
  | Engel of lvl * t list * t
  | Uni of Syntax.uni_level
[@@deriving show, eq]
and extent_head = {var : lvl; dom : clos; mot : clos2; ctx : t; endcase : clos list; varcase : closN}
[@@deriving show, eq]
and head =
  | Var of lvl
  | Ext of extent_head
[@@deriving show, eq]
and cell =
  | Ap of nf
  | Fst
  | Snd
  | BApp of lvl
  | NRec of clos * t * clos2
  | If of clos * t * t
  | J of clos3 * clos * t * t * t
  | Ungel of nf list * closN * clos * (* BBINDER *) lvl * clos * clos
[@@deriving show, eq]
and spine = cell list
[@@deriving show, eq]
and ne = head * spine
[@@deriving show, eq]
and nf =
  | Normal of {tp : t; term : t}
[@@deriving show, eq]

let root h = (h, [])
let (@:) cell (h, s) = (h, cell :: s)

let instantiate_bvar r i j =
  if j = i then r else j

let instantiate_bdim r i = function
  | BVar j -> BVar (instantiate_bvar r i j)
  | Const o -> Const o

let rec instantiate_entry r i = function
  | BDim s -> BDim (instantiate_bdim r i s)
  | Term t -> Term (instantiate r i t)

and instantiate_env r i env =
  List.map (instantiate_entry r i) env

and instantiate_clos r i = function
  | Clos {term; env} -> Clos {term; env = instantiate_env r i env}
  | ConstClos t -> ConstClos (instantiate r i t)

and instantiate_clos2 r i (Clos2 {term; env = env}) =
  Clos2 {term; env = instantiate_env r i env}

and instantiate_clos3 r i (Clos3 {term; env = env}) =
  Clos3 {term; env = instantiate_env r i env}

and instantiate_closN r i (ClosN {term; env = env}) =
  ClosN {term; env = instantiate_env r i env}

and instantiate r i = function
  | Lam clo -> Lam (instantiate_clos r i clo)
  | Neutral {tp; term} ->
    Neutral {tp = instantiate r i tp; term = instantiate_ne r i term}
  | Unit -> Unit
  | Triv -> Triv
  | Nat -> Nat
  | Zero -> Zero
  | Suc t -> Suc (instantiate r i t)
  | Bool -> Bool
  | True -> True
  | False -> False
  | Pi (src, dst) -> Pi (instantiate r i src, instantiate_clos r i dst)
  | Sg (src, dst) -> Sg (instantiate r i src, instantiate_clos r i dst)
  | Pair (t, u) -> Pair (instantiate r i t, instantiate r i u)
  | Bridge (dst, ts) -> Bridge (instantiate_clos r i dst, List.map (instantiate r i) ts)
  | BLam clo -> BLam (instantiate_clos r i clo)
  | Refl t -> Refl (instantiate r i t)
  | Id (ty, t, u) -> Id (instantiate r i ty, instantiate r i t, instantiate r i u)
  | Gel (j, ts, t) -> Gel (instantiate_bvar r i j, List.map (instantiate r i) ts, instantiate_closN r i t)
  | Engel (j, ts, t) -> Engel (instantiate_bvar r i j, List.map (instantiate r i) ts, instantiate r i t)
  | Uni i -> Uni i

and instantiate_extent_head r i {var; dom; mot; ctx; endcase; varcase} =
  {var = instantiate_bvar r i var;
   dom = instantiate_clos r i dom;
   mot = instantiate_clos2 r i mot;
   ctx = instantiate r i ctx;
   endcase = List.map (instantiate_clos r i) endcase;
   varcase = instantiate_closN r i varcase}  

and instantiate_spine : 'a. (lvl -> lvl -> 'a -> 'a) -> lvl -> lvl -> 'a * spine -> 'a * spine =
  fun head_inst ->
  let rec go r i (h, s) =
    match s with
    | [] -> root (head_inst r i h)
    | Ap t :: s -> Ap (instantiate_nf r i t) @: go r i (h, s)
    | Fst :: s -> Fst @: go r i (h, s)
    | Snd :: s -> Snd @: go r i (h, s)
    | BApp j :: s -> BApp (instantiate_bvar r i j) @: go r i (h, s)
    | NRec (tp, zero, suc) :: s ->
      NRec
        (instantiate_clos r i tp,
         instantiate r i zero,
         instantiate_clos2 r i suc)
      @: go r i (h, s)
    | If (mot, tt, ff) :: s ->
      If
        (instantiate_clos r i mot,
         instantiate r i tt,
         instantiate r i ff)
      @: go r i (h, s)
    | J (mot, refl, tp, left, right) :: s ->
      J
        (instantiate_clos3 r i mot,
         instantiate_clos r i refl,
         instantiate r i tp,
         instantiate r i left,
         instantiate r i right)
      @: go r i (h, s)
    | Ungel (ends, rel, mot, j, clo, case) :: s ->
      let j' = if i = j then j else max (r + 1) j in
      let ne = if i = j then (h, s) else go r i (go j' j (h, s))
      in
      Ungel
        (List.map (instantiate_nf r i) ends,
         instantiate_closN r i rel,
         instantiate_clos r i mot,
         j',
         instantiate_clos r i clo,
         instantiate_clos r i case)
      @: ne
  in
  go

and instantiate_ne r i ne =
  let headf r i = function
    | Var j -> Var (instantiate_bvar r i j)
    | Ext e -> Ext (instantiate_extent_head r i e)
  in
  instantiate_spine headf r i ne

and instantiate_nf r i (Normal {tp; term}) =
  Normal {tp = instantiate r i tp; term = instantiate r i term}
