type uni_level = int

type bdim =
  (* | BZero
   * | BOne *)
  | BVar of int

type t =
  | Var of int (* DeBruijn indices for variables & ticks *)
  | Let of t * (* BINDS *) t | Check of t * t
  | Nat | Zero | Suc of t | NRec of (* BINDS *) t * t * (* BINDS 2 *) t * t
  | Pi of t * (* BINDS *) t | Lam of (* BINDS *) t | Ap of t * t
  | Sg of t * (* BINDS *) t | Pair of t * t | Fst of t | Snd of t
  | Id of t * t * t | Refl of t | J of (* BINDS 3 *) t * (* BINDS *) t * t
  | Box of (* BINDS BDIM *) t | Open of t * bdim | Shut of (* BINDS BDIM *) t
  | Uni of uni_level

(* type env_entry =
 *   | BDim
 *   | Term of t
 * type env = env_entry list *)

val equal_uni_level : uni_level -> uni_level -> bool
val equal : t -> t -> bool

val pp_uni_level : Format.formatter -> uni_level -> unit
val show_uni_level : uni_level -> string

val pp_bdim : Format.formatter -> bdim -> unit

val pp : Format.formatter -> t -> unit
val show : t -> string
