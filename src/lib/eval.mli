exception Eval_failed of string

(* Evaluation *)
val eval_bdim : Syntax.bdim -> Domain.env -> Domain.bdim
val eval : Syntax.t -> Domain.env -> int -> Domain.t

(* Functions to manipulate elements of the semantic domain *)
val do_ap : int -> Domain.t -> Domain.t -> Domain.t
val do_bapp : int -> Domain.t -> Domain.bdim -> Domain.t
val do_rec : int -> Domain.clos -> Domain.t -> Domain.clos2 -> Domain.t -> Domain.t
val do_fst : Domain.t -> Domain.t
val do_snd : int -> Domain.t -> Domain.t
val do_j : int -> Domain.clos3 -> Domain.clos -> Domain.t -> Domain.t
val do_ungel : int -> Domain.clos -> int -> Domain.t -> Domain.clos -> Domain.clos -> Domain.t

val do_bclos : int -> Domain.clos -> Domain.bdim -> Domain.t
val do_clos : int -> Domain.clos -> Domain.t -> Domain.t
val do_clos2 : int -> Domain.clos2 -> Domain.t -> Domain.t -> Domain.t
val do_clos3 : int -> Domain.clos3 -> Domain.t -> Domain.t -> Domain.t -> Domain.t
val do_closbclos : int -> Domain.clos2 -> Domain.t -> Domain.bdim -> Domain.t
val do_bclosclos : int -> Domain.clos2 -> Domain.bdim -> Domain.t -> Domain.t
