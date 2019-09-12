type bdim =
  (* | BZero
   * | BOne *)
  | BVar of int

type env_entry =
  | BDim of bdim
  | Term of t
and env = env_entry list
and clos =
    Clos of {term : Syntax.t; env : env}
  | ConstClos of t
and clos2 = Clos2 of {term : Syntax.t; env : env}
and clos3 = Clos3 of {term : Syntax.t; env : env}
and abs = Abs of {var : int; ne : ne}
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
and nf =
  | Normal of {tp : t; term : t}

val mk_bvar : env -> bdim
val mk_var : t -> env -> t

val equal : t -> t -> bool
val equal_ne : ne -> ne -> bool
val equal_nf : nf -> nf -> bool

val pp : Format.formatter -> t -> unit
val pp_bdim : Format.formatter -> bdim -> unit
val pp_nf : Format.formatter -> nf -> unit
val pp_ne : Format.formatter -> ne -> unit
val pp_env : Format.formatter -> env -> unit

val show : t -> string
val show_nf : nf -> string
val show_ne : ne -> string

val subst_bvar_ne : int -> int -> ne -> ne
