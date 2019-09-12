type uni_level = int

type bdim =
  (* | BZero
   * | BOne *)
  | BVar of int (* DeBruijn indices for variables *)

type t =
  | Var of int (* DeBruijn indices for variables *)
  | Let of t * (* BINDS *) t | Check of t * t
  | Nat | Zero | Suc of t | NRec of (* BINDS *) t * t * (* BINDS 2 *) t * t
  | Pi of t * (* BINDS *) t | Lam of (* BINDS *) t | Ap of t * t
  | Sg of t * (* BINDS *) t | Pair of t * t | Fst of t | Snd of t
  | Id of t * t * t | Refl of t | J of (* BINDS 3 *) t * (* BINDS *) t * t
  | Bridge of (* BBINDS *) t | BApp of t * bdim | BLam of (* BBINDS *) t
  | Extent of bdim * (* BBINDS *) t * (* BBINDS & BINDS *) t * t * (* BINDS & BBINDS *) t
  | Gel of bdim * t | Engel of bdim * t | Ungel of (* BBINDS *) t
  | Uni of uni_level

val equal_uni_level : uni_level -> uni_level -> bool
val equal : t -> t -> bool

val lift_bdim : int -> bdim -> bdim
val dim_is_apart_from : depth:int -> bdim -> t -> bool
val extract_bvar : int -> t -> t option

val pp_uni_level : Format.formatter -> uni_level -> unit
val show_uni_level : uni_level -> string

val pp_bdim : Format.formatter -> bdim -> unit

val pp : Format.formatter -> t -> unit
val show : t -> string

