exception Nbe_failed of string

(* Main functions for doing a full normalization *)
(* val normalize : env:Syntax.env -> term:Syntax.t -> tp:Syntax.t -> Syntax.t *)

(* Functions to pass between various semantic domains *)
val eval_bdim : Syntax.bdim -> Domain.env -> Domain.bdim
val eval : Syntax.t -> Domain.env -> Domain.t
val read_back_nf : Domain.env -> Domain.nf -> Syntax.t (* Note that read_back is referred to as quotation in the paper *)
val read_back_tp : Domain.env -> Domain.t -> Syntax.t
val read_back_ne : Domain.env -> Domain.ne -> Syntax.t

val check_nf : Domain.env -> Domain.nf -> Domain.nf -> bool
val check_ne : Domain.env -> Domain.ne -> Domain.ne -> bool
val check_tp : subtype:bool -> Domain.env -> Domain.t -> Domain.t -> bool

(* Functions to manipulate elements of the semantic domain *)
val do_bclos : Domain.clos -> Domain.bdim -> Domain.t
val do_clos : Domain.clos -> Domain.t -> Domain.t
val do_bapp : Domain.t -> Domain.bdim -> Domain.t

val level_to_index : Domain.env -> int -> int
