type idx = int
type uni_level = int

type dim =
  | DVar of idx (* DeBruijn indices for variables *)
  | Const of int

type t =
  | Var of idx (* DeBruijn indices for variables *)
  | Let of t * (* BINDS *) t | Check of t * t
  | Unit | Triv
  | Nat | Zero | Suc of t | NRec of (* BINDS *) t * t * (* BINDS 2 *) t * t
  | List of t | Nil | Cons of t * t | ListRec of (* BINDS *) t * t * (* BINDS 3 *) t * t
  | Bool | True | False | If of (* BINDS *) t * t * t * t
  | Coprod of t * t | Inl of t | Inr of t | Case of (* BINDS *) t * (* BINDS *) t * (* BINDS *) t * t
  | Pi of t * (* BINDS *) t | Lam of (* BINDS *) t | Ap of t * t
  | Sg of t * (* BINDS *) t | Pair of t * t | Fst of t | Snd of t
  | Id of t * t * t | Refl of t | J of (* BINDS 3 *) t * (* BINDS *) t * t
  | Bridge of (* BBINDS *) t * t option list | BApp of t * dim | BLam of (* BBINDS *) t
  | Extent of dim * (* BBINDS *) t * (* BBINDS & BINDS *) t * t * (* BINDS *) t list * (* BINDS & BBINDS *) t
  | Gel of dim * t list * (* BINDS n *) t | Engel of idx * t list * t
  | Ungel of int * (* BINDS *) t * (* BBINDS *) t * (* BINDS *) t
  | Codisc of t | Encodisc of t | Uncodisc of t
  | Global of t | Englobe of t | Unglobe of t
  | Uni of uni_level

val equal_uni_level : uni_level -> uni_level -> bool
val equal_idx : idx -> idx -> bool
val equal : t -> t -> bool

val unsubst_bvar : idx -> t -> t option

val pp_uni_level : Format.formatter -> uni_level -> unit
val show_uni_level : uni_level -> string

val pp_idx : Format.formatter -> idx -> unit
val pp_dim : Format.formatter -> dim -> unit

val pp : Format.formatter -> t -> unit
val show : t -> string

