exception Quote_failed of string

type env_entry =
  | DVar of int
  | Var of {level : Domain.lvl; tp : Domain.t}
  | Def of Domain.t
  | TopLevel of Domain.t
  | Postulate of {level : Domain.lvl; tp : Domain.t}
type env = env_entry list

val env_to_sem_env : env -> Domain.env

val reduce_extent : env -> Domain.lvl -> Domain.extent_head * Domain.spine -> Domain.t option

(* Quotation *)
val read_back_level : env -> Domain.lvl -> Domain.lvl
val read_back_nf : env -> Domain.lvl ->  Domain.nf -> Syntax.t
val read_back_tp : env -> Domain.lvl -> Domain.t -> Syntax.t

val check_nf : env -> Domain.lvl -> Domain.nf -> Domain.nf -> bool
val check_tp : subtype:bool -> env -> Domain.lvl -> Domain.t -> Domain.t -> bool

