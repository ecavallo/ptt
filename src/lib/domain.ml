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
[@@deriving show, eq]
and nf =
  | Normal of {tp : t; term : t}
[@@deriving show, eq]

let mk_bvar env = BVar (List.length env)

let mk_var tp env = Neutral {tp; term = Var (List.length env)}
