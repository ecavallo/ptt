type lvl = int
[@@deriving show{ with_path = false }, eq]

type dim =
  | DVar of lvl
  | Const of int
[@@deriving show, eq]

type env_entry =
  | TopLevel of t
  | Dim of dim
  | Tm of t
and env = env_entry list
[@@deriving show, eq]
and clos =
  | Clos of {term : Syntax.t; env : env}
  | Pseudo of {var : lvl; term : t; ends : t list}
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
  | List of t
  | Nil
  | Cons of t * t
  | Bool
  | True
  | False
  | Coprod of t * t
  | Inl of t
  | Inr of t
  | Pi of t * clos
  | Sg of t * clos
  | Pair of t * t
  | Bridge of clos * t option list
  | BLam of clos
  | Refl of t
  | Id of t * t * t
  | Gel of lvl * t list * closN
  | Engel of lvl * t list * t
  | Codisc of t
  | Encodisc of t
  | Global of t
  | Englobe of t
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
  | BApp of dim
  | NRec of clos * t * clos2
  | ListRec of t * clos * t * clos3
  | If of clos * t * t
  | Case of t * t * clos * clos * clos
  | J of clos3 * clos * t * t * t
  | Ungel of t list * t * t * clos * (* BBINDER *) lvl * clos
  | Uncodisc
  | Unglobe
  | Quasi of quasi_cell
[@@deriving show, eq]
and quasi_cell = 
  | PiDom
  | PiCod of t
  | SgDom
  | SgCod of t
  | ListTp
  | CoprodLeft
  | CoprodRight
  | IdTp
  | IdLeft
  | IdRight
  | BridgeCod of dim
  | BridgeEndpoint of ne * int
  | GelRel of t list
  | GelBridge of t list
  | CodiscTp
  | GlobalTp
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

let instantiate_dim r i = function
  | DVar j -> DVar (instantiate_bvar r i j)
  | Const o -> Const o

let rec instantiate_entry r i = function
  | TopLevel t -> TopLevel t
  | Dim s -> Dim (instantiate_dim r i s)
  | Tm t -> Tm (instantiate r i t)

and instantiate_env r i env =
  List.map (instantiate_entry r i) env

and instantiate_clos r i = function
  | Clos {term; env} ->
    Clos {term; env = instantiate_env r i env}
  | Pseudo {var; term; ends} ->
    let var' = if i = var then var else max (r + 1) var in
    let term' = if i = var then term else instantiate r i (instantiate var' var term) in
    let ends' = List.map (instantiate r i) ends in
    Pseudo {var = var'; term = term'; ends = ends'}

and instantiate_clos2 r i (Clos2 {term; env}) =
  Clos2 {term; env = instantiate_env r i env}

and instantiate_clos3 r i (Clos3 {term; env}) =
  Clos3 {term; env = instantiate_env r i env}

and instantiate_closN r i (ClosN {term; env}) =
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
  | List t -> List (instantiate r i t)
  | Nil -> Nil
  | Cons (a, t) -> Cons (instantiate r i a, instantiate r i t)
  | Bool -> Bool
  | True -> True
  | False -> False
  | Coprod (t1, t2) -> Coprod (instantiate r i t1, instantiate r i t2)
  | Inl t -> Inl (instantiate r i t)
  | Inr t -> Inr (instantiate r i t)
  | Pi (src, dst) -> Pi (instantiate r i src, instantiate_clos r i dst)
  | Sg (src, dst) -> Sg (instantiate r i src, instantiate_clos r i dst)
  | Pair (t, u) -> Pair (instantiate r i t, instantiate r i u)
  | Bridge (dst, ts) -> Bridge (instantiate_clos r i dst, List.map (Option.map (instantiate r i)) ts)
  | BLam clo -> BLam (instantiate_clos r i clo)
  | Refl t -> Refl (instantiate r i t)
  | Id (ty, t, u) -> Id (instantiate r i ty, instantiate r i t, instantiate r i u)
  | Gel (j, ts, t) -> Gel (instantiate_bvar r i j, List.map (instantiate r i) ts, instantiate_closN r i t)
  | Engel (j, ts, t) -> Engel (instantiate_bvar r i j, List.map (instantiate r i) ts, instantiate r i t)
  | Codisc t -> Codisc (instantiate r i t)
  | Encodisc t -> Encodisc (instantiate r i t)
  | Global t -> Global (instantiate r i t)
  | Englobe t -> Englobe (instantiate r i t)
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
    | BApp t :: s -> BApp (instantiate_dim r i t) @: go r i (h, s)
    | NRec (tp, zero, suc) :: s ->
      NRec
        (instantiate_clos r i tp,
         instantiate r i zero,
         instantiate_clos2 r i suc)
      @: go r i (h, s)
    | ListRec (tp, mot, nil, cons) :: s ->
      ListRec
        (instantiate r i tp,
         instantiate_clos r i mot,
         instantiate r i nil,
         instantiate_clos3 r i cons)
      @: go r i (h, s)
    | If (mot, tt, ff) :: s ->
      If
        (instantiate_clos r i mot,
         instantiate r i tt,
         instantiate r i ff)
      @: go r i (h, s)
    | Case (left, right, mot, inl, inr) :: s ->
      Case
        (instantiate r i left,
         instantiate r i right,
         instantiate_clos r i mot,
         instantiate_clos r i inl,
         instantiate_clos r i inr)
      @: go r i (h, s)
    | J (mot, refl, tp, left, right) :: s ->
      J
        (instantiate_clos3 r i mot,
         instantiate_clos r i refl,
         instantiate r i tp,
         instantiate r i left,
         instantiate r i right)
      @: go r i (h, s)
    | Ungel (ends, ty, bri, mot, j, case) :: s ->
      let j' = if i = j then j else max (r + 1) j in
      let ne = if i = j then (h, s) else go r i (go j' j (h, s))
      in
      Ungel
        (List.map (instantiate r i) ends,
         instantiate r i ty,
         instantiate r i bri,
         instantiate_clos r i mot,
         j',
         instantiate_clos r i case)
      @: ne
    | Quasi q :: s -> Quasi (instantiate_quasi_cell r i q) @: go r i (h, s)
    | Unglobe :: s -> Unglobe @: go r i (h, s)
    | Uncodisc :: s -> Uncodisc @: go r i (h, s)
  in
  go

and instantiate_quasi_cell r i =
  function 
  | PiDom -> PiDom 
  | PiCod v -> PiCod (instantiate r i v)
  | SgDom -> SgDom 
  | SgCod v -> SgCod (instantiate r i v)
  | ListTp -> ListTp
  | CoprodLeft -> CoprodLeft
  | CoprodRight -> CoprodRight
  | IdLeft -> IdLeft
  | IdRight -> IdRight
  | IdTp -> IdTp
  | BridgeCod s -> BridgeCod (instantiate_dim r i s)
  | BridgeEndpoint (t, o) -> BridgeEndpoint (instantiate_ne r i t, o)
  | GelRel ts -> GelRel (List.map (instantiate r i) ts)
  | GelBridge ts -> GelBridge (List.map (instantiate r i) ts)
  | CodiscTp -> CodiscTp
  | GlobalTp -> GlobalTp

and instantiate_ne r i ne =
  let headf r i = function
    | Var j -> Var (instantiate_bvar r i j)
    | Ext e -> Ext (instantiate_extent_head r i e)
  in
  instantiate_spine headf r i ne

and instantiate_nf r i (Normal {tp; term}) =
  Normal {tp = instantiate r i tp; term = instantiate r i term}
