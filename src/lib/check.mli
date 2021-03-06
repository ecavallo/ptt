type error =
    Cannot_synth_term of Syntax.t
  | Mode_mismatch of Mode.mode * Mode.mode
  | Dim_mismatch of Domain.dim * Domain.dim
  | Type_mismatch of Syntax.t * Syntax.t
  | Expecting_universe of Domain.t
  | Expecting_term of Domain.lvl
  | Expecting_of of string * Domain.t
  | Misc of string

val pp_error : Format.formatter -> error -> unit

exception Type_error of error

type env_entry =
  | DVar of {level : Domain.lvl; width : int}
  | Var of {level : Domain.lvl; tp : Domain.t; modality : Mode.modality}
  | Def of {term : Domain.t; tp : Domain.t}
  | Restrict of Syntax.idx
  | Lock of Mode.modality
  | TopLevel of {mode : Mode.mode; term : Domain.t; tp : Domain.t}
  | Postulate of {mode : Mode.mode; level : Domain.lvl; tp : Domain.t}

type env = env_entry list

val env_to_sem_env : env -> Domain.env
val env_to_quote_env : env -> Quote.env

val check : mode:Mode.mode -> env:env -> size:Domain.lvl -> term:Syntax.t -> tp:Domain.t -> unit
val synth : mode:Mode.mode -> env:env -> size:Domain.lvl -> term:Syntax.t -> Domain.t
val check_tp : mode:Mode.mode -> env:env -> size:Domain.lvl -> term:Syntax.t -> unit
