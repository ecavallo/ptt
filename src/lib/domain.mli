type lvl = int

type dim =
  | DVar of lvl
  | Const of int

type env_entry =
  | TopLevel of t
  | Dim of dim
  | Tm of t
and env = env_entry list
and clos =
  | Clos of {term : Syntax.t; env : env}
  | Pseudo of {var : lvl; term : t; ends : t list}
and clos2 = Clos2 of {term : Syntax.t; env : env}
and clos3 = Clos3 of {term : Syntax.t; env : env}
and closN = ClosN of {term : Syntax.t; env : env}
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
  | Void
  | Pi of t * clos
  | Sg of t * clos
  | Pair of t * t
  | Bridge of clos * t option list
  | BLam of clos
  | Refl of t
  | Id of t * t * t
  | Gel of lvl * t list * closN
  | Engel of lvl * t list * t
  | Global of t
  | Englobe of t
  | Disc of t
  | Endisc of t
  | Uni of Syntax.uni_level
and extent_head = {var : lvl; dom : clos; mot : clos2; ctx : t; endcase : clos list; varcase : closN}
and head =
  | Var of lvl
  | Ext of extent_head
and cell =
  | Ap of nf
  | Fst
  | Snd
  | BApp of dim
  | NRec of clos * t * clos2
  | ListRec of t * clos * t * clos3
  | If of clos * t * t
  | Case of t * t * clos * clos * clos
  | Abort of clos
  | J of clos3 * clos * t * t * t
  | Ungel of t list * t * t * clos * (* BBINDER *) lvl * clos
  | Unglobe
  | Letdisc of Mode.modality * t * clos * clos
  | Quasi of quasi_cell
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
  | GlobalTp
  | DiscTp
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
val pp_dim : Format.formatter -> dim -> unit
val pp_nf : Format.formatter -> nf -> unit
val pp_ne : Format.formatter -> ne -> unit
val pp_env : Format.formatter -> env -> unit

val show : t -> string
val show_nf : nf -> string
val show_ne : ne -> string
