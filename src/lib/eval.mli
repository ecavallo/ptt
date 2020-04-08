exception Eval_failed of string

(* Evaluation *)
val eval_dim : Syntax.dim -> Domain.env -> Domain.dim
val eval : Syntax.t -> Domain.env -> Domain.lvl -> Domain.t

(* Functions to manipulate elements of the semantic domain *)
val do_ap : Domain.lvl -> Domain.t -> Domain.t -> Domain.t
val do_bapp : Domain.lvl -> Domain.t -> Domain.dim -> Domain.t
val do_rec : Domain.lvl -> Domain.clos -> Domain.t -> Domain.clos2 -> Domain.t -> Domain.t
val do_list_rec : Domain.lvl -> Domain.clos -> Domain.t -> Domain.clos3 -> Domain.t -> Domain.t
val do_if : Domain.lvl -> Domain.clos -> Domain.t -> Domain.t -> Domain.t -> Domain.t
val do_case : Domain.lvl -> Domain.clos -> Domain.clos -> Domain.clos -> Domain.t -> Domain.t
val do_abort : Domain.lvl -> Domain.clos -> Domain.t -> Domain.t
val do_fst : Domain.t -> Domain.t
val do_snd : Domain.lvl -> Domain.t -> Domain.t
val do_j : Domain.lvl -> Domain.clos3 -> Domain.clos -> Domain.t -> Domain.t
val do_ungel : Domain.lvl -> Domain.t list -> Domain.clos -> Domain.t -> Domain.clos -> Domain.t
val do_unglobe : Domain.t -> Domain.t
val do_letdisc : Domain.lvl -> Mode.modality -> Domain.clos -> Domain.clos -> Domain.t -> Domain.t

val do_pi_dom : Domain.t -> Domain.t
val do_pi_cod : Domain.lvl -> Domain.t -> Domain.t -> Domain.t
val do_sg_dom : Domain.t -> Domain.t
val do_sg_cod : Domain.lvl -> Domain.t -> Domain.t -> Domain.t
val do_list_tp : Domain.t -> Domain.t
val do_coprod_left : Domain.t -> Domain.t
val do_coprod_right : Domain.t -> Domain.t
val do_id_left : Domain.t -> Domain.t
val do_id_right : Domain.t -> Domain.t
val do_id_tp : Domain.t -> Domain.t
val do_bridge_cod : Domain.lvl -> Domain.t -> Domain.dim -> Domain.t
val do_bridge_endpoint : Domain.lvl -> Domain.t -> Domain.ne -> int -> Domain.t
val do_gel_rel : Domain.lvl -> Domain.t -> Domain.t list -> Domain.t
val do_gel_bridge : Domain.lvl -> Domain.t -> Domain.t list -> Domain.t
val do_global_tp : Domain.t -> Domain.t
val do_disc_tp : Domain.t -> Domain.t

val do_clos : Domain.lvl -> Domain.clos -> Domain.env_entry -> Domain.t
val do_clos2 : Domain.lvl -> Domain.clos2 -> Domain.env_entry -> Domain.env_entry -> Domain.t
val do_clos3 : Domain.lvl -> Domain.clos3 -> Domain.t -> Domain.t -> Domain.t -> Domain.t
val do_closN : Domain.lvl -> Domain.closN -> Domain.t list -> Domain.t
val do_clos_extent : Domain.lvl -> Domain.closN -> Domain.t list -> Domain.t -> Domain.dim -> Domain.t
val do_consts : Domain.lvl -> Domain.clos -> int -> Domain.t list
