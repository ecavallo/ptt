exception Eval_failed of string

(* Evaluation *)
val eval_bdim : Syntax.bdim -> Domain.env -> Domain.bdim
val eval : Syntax.t -> Domain.env -> Domain.lvl -> Domain.t

(* Functions to manipulate elements of the semantic domain *)
val do_ap : Domain.lvl -> Domain.t -> Domain.t -> Domain.t
val do_bapp : Domain.lvl -> Domain.t -> Domain.bdim -> Domain.t
val do_rec : Domain.lvl -> Domain.clos -> Domain.t -> Domain.clos2 -> Domain.t -> Domain.t
val do_if : Domain.lvl -> Domain.clos -> Domain.t -> Domain.t -> Domain.t -> Domain.t
val do_fst : Domain.t -> Domain.t
val do_snd : Domain.lvl -> Domain.t -> Domain.t
val do_j : Domain.lvl -> Domain.clos3 -> Domain.clos -> Domain.t -> Domain.t
val do_ungel : Domain.lvl -> Domain.clos -> Domain.t -> Domain.clos -> Domain.clos -> Domain.t

val do_bclos : Domain.lvl -> Domain.clos -> Domain.bdim -> Domain.t
val do_clos : Domain.lvl -> Domain.clos -> Domain.t -> Domain.t
val do_clos2 : Domain.lvl -> Domain.clos2 -> Domain.t -> Domain.t -> Domain.t
val do_clos3 : Domain.lvl -> Domain.clos3 -> Domain.t -> Domain.t -> Domain.t -> Domain.t
val do_closN : Domain.lvl -> Domain.closN -> Domain.t list -> Domain.t
val do_closbclos : Domain.lvl -> Domain.clos2 -> Domain.t -> Domain.bdim -> Domain.t
val do_bclosclos : Domain.lvl -> Domain.clos2 -> Domain.bdim -> Domain.t -> Domain.t
val do_clos_extent : Domain.lvl -> Domain.closN -> Domain.t list -> Domain.t -> Domain.bdim -> Domain.t
val do_consts : Domain.lvl -> Domain.clos -> int -> Domain.t list
