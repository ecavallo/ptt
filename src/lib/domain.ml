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
  | Extent of {var : int; dom : clos; mot : clos2; ctx : t; varcase : clos2; stack : stack}
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
and cell =
  | Ap of nf
  | Fst
  | Snd
  | BApp of int
  | NRec of clos * t * clos2
  | J of clos3 * clos * t * t * t
  | Ungel of env
[@@deriving show, eq]
and stack = cell list
[@@deriving show, eq]
and ne = int * stack (* DeBruijn levels for variables *)
[@@deriving show, eq]
and nf =
  | Normal of {tp : t; term : t}
[@@deriving show, eq]

let mk_bvar env = BVar (List.length env)

let mk_var tp env = Neutral {tp; term = (List.length env, [])}

let rec stack_env env = function
  | [] -> env
  | Ungel env :: stack -> stack_env env stack
  | _ :: stack -> stack_env env stack
