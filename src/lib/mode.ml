exception Modality_failure of string

type mode =
  | Pointwise
  | Parametric
[@@deriving show{ with_path = false }, eq]

type modality =
  | IdPointwise
  | IdParametric
  | Components
  | Discrete
  | Global
  | DiscreteComponents
  | DiscreteGlobal
[@@deriving show{ with_path = false }, eq]

let id = function
  | Pointwise -> IdPointwise
  | Parametric -> IdParametric

let src = function
  | IdPointwise -> Pointwise
  | IdParametric -> Parametric
  | Components -> Parametric
  | Discrete -> Pointwise
  | Global -> Parametric
  | DiscreteComponents -> Parametric
  | DiscreteGlobal -> Parametric

let dst = function
  | IdPointwise -> Pointwise
  | IdParametric -> Parametric
  | Components -> Pointwise
  | Discrete -> Parametric
  | Global -> Pointwise
  | DiscreteComponents -> Parametric
  | DiscreteGlobal -> Parametric

let compose m1 m2 =
  match m1, m2 with
  | IdPointwise, _ -> m2
  | _, IdPointwise -> m1
  | IdParametric, _ -> m2
  | _, IdParametric -> m1
  | Components, Discrete -> IdPointwise
  | Components, DiscreteComponents -> Components
  | Components, DiscreteGlobal -> Global
  | Discrete, Components -> DiscreteComponents
  | Discrete, Global -> DiscreteGlobal
  | Global, Discrete -> IdPointwise
  | Global, DiscreteComponents -> Components
  | Global, DiscreteGlobal -> Global
  | DiscreteComponents, Discrete -> Discrete
  | DiscreteComponents, DiscreteComponents -> DiscreteComponents
  | DiscreteComponents, DiscreteGlobal -> DiscreteGlobal
  | DiscreteGlobal, Discrete -> Discrete
  | DiscreteGlobal, DiscreteComponents -> DiscreteComponents
  | DiscreteGlobal, DiscreteGlobal -> DiscreteGlobal
  | _ -> raise (Modality_failure ("Tried to compose mismatched modalities" ^ show_modality m1 ^ " and " ^ show_modality m2))

let leq m1 m2 =
  match m1, m2 with
  | IdPointwise, IdPointwise -> true
  | IdParametric, IdParametric -> true
  | IdParametric, DiscreteComponents -> true
  | IdParametric, DiscreteGlobal -> false
  | Components, Components -> true
  | Components, Global -> false
  | Discrete, Discrete -> true
  | Global, Components -> true
  | Global, Global -> true
  | DiscreteComponents, IdParametric -> false
  | DiscreteComponents, DiscreteComponents -> true
  | DiscreteComponents, DiscreteGlobal -> false
  | DiscreteGlobal, IdParametric -> true
  | DiscreteGlobal, DiscreteComponents -> true
  | DiscreteGlobal, DiscreteGlobal -> true
  | _ -> raise (Modality_failure ("Tried to compare mismatched modalities " ^ show_modality m1 ^ " and " ^ show_modality m2))

let show_mode = function
  | Pointwise -> "pt"
  | Parametric -> "par"

let show_modality = function
  | IdPointwise -> "."
  | IdParametric -> "."
  | Components -> ".components"
  | Discrete -> ".discrete"
  | Global -> ".global"
  | DiscreteComponents -> ".components.discrete"
  | DiscreteGlobal -> ".global.discrete"
