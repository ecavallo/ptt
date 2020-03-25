type mode =
  | Pointwise
  | Parametric

type modality =
  | IdPointwise
  | IdParametric
  | Components
  | Discrete
  | Global
  | DiscreteComponents
  | DiscreteGlobal

val equal_mode : mode -> mode -> bool
val equal_modality : modality -> modality -> bool

val pp_mode : Format.formatter -> mode -> unit
val pp_modality : Format.formatter -> modality -> unit

val show_mode : mode -> string
val show_modality : modality -> string

val id : mode -> modality
val src : modality -> mode
val dst : modality -> mode
val compose : modality -> modality -> modality
val leq : modality -> modality -> bool
