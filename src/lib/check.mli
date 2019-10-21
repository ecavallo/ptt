type error =
    Cannot_synth_term of Syntax.t
  | BDim_mismatch of Domain.bdim * Domain.bdim
  | Type_mismatch of Domain.t * Domain.t
  | Expecting_universe of Domain.t
  | Expecting_term of int
  | Misc of string

val pp_error : Format.formatter -> error -> unit

exception Type_error of error

type env_entry =
  | BVar of int
  | Var of {level : int; tp : Domain.t}
  | Def of {term : Domain.t; tp : Domain.t}
  | Restrict of int

type env = env_entry list

val env_to_sem_env : env -> Domain.env
val env_to_quote_env : env -> Quote.env

val check : env:env -> size:int -> term:Syntax.t -> tp:Domain.t -> unit
val synth : env:env -> size:int -> term:Syntax.t -> Domain.t
val check_tp : env:env -> size:int -> term:Syntax.t -> unit
