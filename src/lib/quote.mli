exception Quote_failed of string

type env_entry =
  | BVar of int
  | Var of {level : int; tp : Domain.t}
  | Def of {term : Domain.t; tp : Domain.t}
[@@deriving show]
type env = env_entry list
[@@deriving show]

val mk_bvar : env -> int -> Domain.bdim * env
val mk_var : Domain.t -> env -> int -> Domain.t * env

val restrict_env : Domain.bdim -> env -> env
val env_to_sem_env : env -> Domain.env

(* Quotation *)
val read_back_level : env -> int -> int
val read_back_nf : env -> int ->  Domain.nf -> Syntax.t
val read_back_tp : env -> int -> Domain.t -> Syntax.t

val check_nf : env -> int -> Domain.nf -> Domain.nf -> bool
val check_tp : subtype:bool -> env -> int -> Domain.t -> Domain.t -> bool

