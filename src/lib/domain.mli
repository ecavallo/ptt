type lvl = int

type bdim =
  | BVar of lvl

type env_entry =
  | BDim of bdim
  | Term of t
and env = env_entry list
and clos =
    Clos of {term : Syntax.t; env : env}
  | ConstClos of t
and clos2 = Clos2 of {term : Syntax.t; env : env}
and clos3 = Clos3 of {term : Syntax.t; env : env}
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
  | Gel of lvl * t
  | Engel of lvl * t
  | Uni of Syntax.uni_level
and extent_head = {var : lvl; dom : clos; mot : clos2; ctx : t; varcase : clos2}
and head =
  | Var of lvl
  | Ext of extent_head
and cell =
  | Ap of nf
  | Fst
  | Snd
  | BApp of lvl
  | NRec of clos * t * clos2
  | J of clos3 * clos * t * t * t
  | Ungel of t * clos * (* BBINDER *) lvl * clos * clos
and spine = cell list
and ne = head * spine
and nf =
  | Normal of {tp : t; term : t}

val root : 'a -> 'a * spine
val (@:) : cell -> 'a * spine -> 'a * spine

val instantiate : lvl -> lvl -> t -> t
val instantiate_bvar : lvl -> lvl -> lvl -> lvl
val instantiate_extent_head : lvl -> lvl -> extent_head -> extent_head
val instantiate_spine : (lvl -> lvl -> 'a -> 'a) -> lvl -> lvl -> 'a * spine -> 'a * spine
val instantiate_ne : lvl -> lvl -> ne -> ne

val equal : t -> t -> bool
val equal_lvl : lvl -> lvl -> bool
val equal_ne : ne -> ne -> bool
val equal_nf : nf -> nf -> bool

val pp : Format.formatter -> t -> unit
val pp_lvl : Format.formatter -> lvl -> unit
val pp_bdim : Format.formatter -> bdim -> unit
val pp_nf : Format.formatter -> nf -> unit
val pp_ne : Format.formatter -> ne -> unit
val pp_env : Format.formatter -> env -> unit

val show : t -> string
val show_nf : nf -> string
val show_ne : ne -> string
