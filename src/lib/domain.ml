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
and extent_root = Ext of {var : int; dom : clos; mot : clos2; ctx : t; varcase : clos2}
[@@deriving show, eq]
and t =
  | Lam of clos
  | Neutral of {tp : t; term : ne}
  | Extent of {tp : t; term : extent_root stack}
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
and 'a stack =
  | Root of 'a
  | Ap of 'a stack * nf
  | Fst of 'a stack
  | Snd of 'a stack
  | BApp of 'a stack * int
  | NRec of clos * t * clos2 * 'a stack
  | J of clos3 * clos * t * t * t * 'a stack
  | Ungel of (* BBINDER *) int * 'a stack
[@@deriving show, eq]
and ne = int stack (* DeBruijn levels for variables *)
[@@deriving show, eq]
and nf =
  | Normal of {tp : t; term : t}
[@@deriving show, eq]

let mk_bvar env = BVar (List.length env)

let mk_var tp env = Neutral {tp; term = Root (List.length env)}

(* instantiate_* r i assumes that i is (at least) the largest free level occurring in the input *)

let instantiate_bvar r i j =
  if j = i then r else j

let instantiate_bdim r i = function
  | BVar j -> BVar (instantiate_bvar r i j)

let rec instantiate_entry r i = function
  | BDim s -> BDim (instantiate_bdim r i s)
  | Term t -> Term (instantiate r i t)

and instantiate_clos r i = function
  | Clos {term; env} -> Clos {term; env = List.map (instantiate_entry r i) env}
  | ConstClos t -> ConstClos (instantiate r i t)

and instantiate_clos2 r i (Clos2 {term; env = env}) =
  Clos2 {term; env = List.map (instantiate_entry r i) env}

and instantiate_clos3 r i (Clos3 {term; env = env}) =
  Clos3 {term; env = List.map (instantiate_entry r i) env}

and instantiate r i = function
  | Lam clo -> Lam (instantiate_clos r i clo)
  | Neutral {tp; term} ->
    Neutral {tp = instantiate r i tp; term = instantiate_ne r i term}
  | Extent {tp; term} ->
    Extent {tp = instantiate r i tp; term = instantiate_extent r i term}
  | Nat -> Nat
  | Zero -> Zero
  | Suc t -> Suc (instantiate r i t)
  | Pi (src, dst) -> Pi (instantiate r i src, instantiate_clos r i dst)
  | Sg (src, dst) -> Sg (instantiate r i src, instantiate_clos r i dst)
  | Pair (t, u) -> Pair (instantiate r i t, instantiate r i u)
  | Bridge dst -> Bridge (instantiate_clos r i dst)
  | BLam clo -> BLam (instantiate_clos r i clo)
  | Refl t -> Refl (instantiate r i t)
  | Id (ty, t, u) -> Id (instantiate r i ty, instantiate r i t, instantiate r i u)
  | Gel (j, t) -> Gel (instantiate_bvar r i j, t)
  | Engel (j, t) -> Engel (instantiate_bvar r i j, t)
  | Uni i -> Uni i

and instantiate_stack : 'a. (int -> int -> 'a -> 'a) -> int -> int -> 'a stack -> 'a stack =
  fun rootf r i ->
  function
  | Root t -> Root (rootf r i t)
  | Ap (s, t) -> Ap (instantiate_stack rootf r i s, instantiate_nf r i t)
  | Fst s -> Fst (instantiate_stack rootf r i s)
  | Snd s -> Snd (instantiate_stack rootf r i s)
  | BApp (s, j) -> BApp (instantiate_stack rootf r i s, instantiate_bvar r i j)
  | NRec (tp, zero, suc, s) ->
    NRec
      (instantiate_clos r i tp,
       instantiate r i zero,
       instantiate_clos2 r i suc,
       instantiate_stack rootf r i s)
  | J (mot, refl, tp, left, right, s) ->
    J
      (instantiate_clos3 r i mot,
       instantiate_clos r i refl,
       instantiate r i tp,
       instantiate r i left,
       instantiate r i right,
       instantiate_stack rootf r i s)
  | Ungel (j, s) ->
    let j' = i + 1 in
    Ungel (j', instantiate_stack rootf r i (instantiate_stack rootf j' j s))

and instantiate_ne r i = instantiate_stack instantiate_bvar r i

and instantiate_extent_root r i (Ext {var; dom; mot; ctx; varcase}) =
  Ext
    {var = instantiate_bvar r i var;
     dom = instantiate_clos r i dom;
     mot = instantiate_clos2 r i mot;
     ctx = instantiate r i ctx;
     varcase = instantiate_clos2 r i varcase}

and instantiate_extent r i = instantiate_stack instantiate_extent_root r i

and instantiate_nf r i (Normal {tp; term}) =
  Normal {tp = instantiate r i tp; term = instantiate r i term}
