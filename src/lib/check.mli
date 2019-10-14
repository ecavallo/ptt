type error =
    Cannot_synth_term of Syntax.t
  | BDim_mismatch of Domain.bdim * Domain.bdim
  | Type_mismatch of Domain.t * Domain.t
  | Expecting_universe of Domain.t
  | Expecting_term of int
  | Misc of string

val pp_error : Format.formatter -> error -> unit

exception Type_error of error

val check : env:Quote.env -> size:int -> term:Syntax.t -> tp:Domain.t -> unit
val synth : env:Quote.env -> size:int -> term:Syntax.t -> Domain.t
val check_tp : env:Quote.env -> size:int -> term:Syntax.t -> unit
