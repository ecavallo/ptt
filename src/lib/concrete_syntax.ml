type ident = string
type uni_level = int

type bdim =
  | BVar of ident

(* module Ints =
 *   struct
 *     type t = int
 *     let compare = Stdlib.compare
 *    end
 * 
 * module DM = Set.Make(Ints)
 * 
 * type dim_set = DM.t *)
          
type binder = Binder of {name : ident; body : t}
and bindern = BinderN of {names : ident list; body : t}
and binder2 = Binder2 of {name1 : ident; name2 : ident; body : t}
and binder3 = Binder3 of {name1 : ident; name2 : ident; name3 : ident; body : t}
and bbindern = BBinderN of {names : ident list; body : t}
and cell = Cell of {name : ident; ty : t}
and spine = Term of t
and t =
  | Var of ident
  | Let of t * binder
  | Check of {term : t; tp : t}
  | Nat
  | Suc of t
  | Lit of int
  | NRec of {mot : binder; zero : t; suc : binder2; nat : t}
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
  | Box of ident list * t
  | Open of t * bdim list
  | Shut of bbindern
  | Uni of uni_level

type decl =
    Def of {name : ident; def : t; tp : t}
  | NormalizeDef of ident
  | NormalizeTerm of {term : t; tp : t}
  | Quit

type signature = decl list
