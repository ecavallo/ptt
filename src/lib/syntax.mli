type idx = int
type uni_level = int

type bdim =
  | BVar of idx (* DeBruijn indices for variables *)
  | Const of int

type t =
  | Var of idx (* DeBruijn indices for variables *)
  | Let of t * (* BINDS *) t | Check of t * t
  | Unit | Triv
  | Nat | Zero | Suc of t | NRec of (* BINDS *) t * t * (* BINDS 2 *) t * t
  | Bool | True | False | If of (* BINDS *) t * t * t * t
  | Pi of t * (* BINDS *) t | Lam of (* BINDS *) t | Ap of t * t
  | Sg of t * (* BINDS *) t | Pair of t * t | Fst of t | Snd of t
  | Id of t * t * t | Refl of t | J of (* BINDS 3 *) t * (* BINDS *) t * t
  | Bridge of (* BBINDS *) t * t list | BApp of t * bdim | BLam of (* BBINDS *) t
  | Extent of bdim * (* BBINDS *) t * (* BBINDS & BINDS *) t * t * (* BINDS *) t list * (* BINDS & BBINDS *) t
  | Gel of bdim * t list * (* BINDS n *) t | Engel of bdim * t list * t
  | Ungel of int * (* BINDS *) t * (* BBINDS *) t * (* BINDS *) t
  | Uni of uni_level

val equal_uni_level : uni_level -> uni_level -> bool
val equal_idx : idx -> idx -> bool
val equal : t -> t -> bool

val unsubst_bvar : idx -> t -> t option

val pp_uni_level : Format.formatter -> uni_level -> unit
val show_uni_level : uni_level -> string

val pp_idx : Format.formatter -> idx -> unit
val pp_bdim : Format.formatter -> bdim -> unit

val pp : Format.formatter -> t -> unit
val show : t -> string

