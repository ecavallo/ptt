type env_entry =
  | BDim of Domain.bdim
  | Term of {term : Domain.t; tp : Domain.t}
  | TopLevel of {term : Domain.t; tp : Domain.t}
type env = env_entry list

val env_to_sem_env : env -> Domain.env

type error =
    Cannot_synth_term of Syntax.t
  | Type_mismatch of Domain.t * Domain.t
  | Expecting_universe of Domain.t
  | Expecting_term of Domain.bdim
  | Misc of string

val pp_error : Format.formatter -> error -> unit

exception Type_error of error

val check : env:env -> size:int -> term:Syntax.t -> tp:Domain.t -> unit
val synth : env:env -> size:int -> term:Syntax.t -> Domain.t
val check_tp : env:env -> size:int -> term:Syntax.t -> unit
