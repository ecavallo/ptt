type ident = string
type uni_level = int

type dim =
  | DVar of ident
  | Const of int

type binder = Binder of {name : ident; body : t}
and bindern = BinderN of {names : ident list; body : t}
and binder2 = Binder2 of {name1 : ident; name2 : ident; body : t}
and binder3 = Binder3 of {name1 : ident; name2 : ident; name3 : ident; body : t}
and cell = Cell of {name : ident; ty : t}
and spine = Term of t | Dim of dim
and t =
  | Var of ident
  | Let of t * binder
  | Check of {term : t; tp : t}
  | Unit
  | Triv
  | Nat
  | Suc of t
  | Lit of int
  | NRec of {mot : binder; zero : t; suc : binder2; nat : t}
  | List of t
  | Nil
  | Cons of t * t
  | ListRec of {mot : binder; nil : t; cons : binder3; list : t}
  | Bool
  | True
  | False
  | If of {mot : binder; tt : t; ff : t; bool : t}
  | Coprod of t * t
  | Inl of t
  | Inr of t
  | Case of {mot : binder; inl : binder; inr : binder; coprod : t}
  | Void
  | Abort of {mot : binder; void : t}
  | Pi of cell list * t
  | Lam of bindern
  | Ap of t * spine list
  | Sg of cell list * t
  | Pair of t * t
  | Fst of t
  | Snd of t
  | Id of t * t * t
  | Refl of t
  | J of {mot : binder3; refl : binder; eq : t}
  | Bridge of binder * t option list
  | BLam of bindern
  | Extent of {dim : dim; dom : binder; mot : binder2; ctx : t; endcase : binder list; varcase : bindern}
  | Gel of dim * t list * bindern
  | Engel of ident * t list * t
  | Ungel of {width : int; mot : binder; gel : binder; case : binder}
  | Codisc of t
  | Encodisc of t
  | Uncodisc of t
  | Global of t
  | Englobe of t
  | Unglobe of t
  | Disc of t
  | Endisc of t
  | Letdisc of {modality : Mode.modality; mot : binder; case : binder; disc : t}
  | Letdiscbridge of {modality : Mode.modality; width : int; mot: binder; case : binder; disc : binder}
  | Uni of uni_level

type decl =
    Def of {name : ident; mode : Mode.mode; def : t; tp : t}
  | Postulate of {name : ident; mode : Mode.mode; tp : t}
  | NormalizeDef of ident
  | NormalizeTerm of {term : t; mode : Mode.mode; tp : t}
  | Quit

type signature = decl list
