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
  | DiscreteComponents
[@@deriving show{ with_path = false }, eq]

let id = function
  | Pointwise -> IdPointwise
  | Parametric -> IdParametric

let src = function
  | IdPointwise -> Pointwise
  | IdParametric -> Parametric
  | Components -> Parametric
  | Discrete -> Pointwise
  | DiscreteComponents -> Parametric

let dst = function
  | IdPointwise -> Pointwise
  | IdParametric -> Parametric
  | Components -> Pointwise
  | Discrete -> Parametric
  | DiscreteComponents -> Parametric

let compose m1 m2 =
  match m1, m2 with
  | IdPointwise, _ -> m2
  | _, IdPointwise -> m1
  | IdParametric, _ -> m2
  | _, IdParametric -> m1
  | Components, Discrete -> IdPointwise
  | Components, DiscreteComponents -> Components
  | Discrete, Components -> DiscreteComponents
  | DiscreteComponents, Discrete -> Discrete
  | DiscreteComponents, DiscreteComponents -> DiscreteComponents
  | _ -> raise (Modality_failure ("Tried to compose mismatched modalities" ^ show_modality m1 ^ " and " ^ show_modality m2))

let leq m1 m2 =
  match m1, m2 with
  | IdPointwise, IdPointwise -> true
  | IdParametric, IdParametric -> true
  | IdParametric, DiscreteComponents -> true
  | Components, Components -> true
  | Discrete, Discrete -> true
  | DiscreteComponents, IdParametric -> false
  | DiscreteComponents, DiscreteComponents -> true
  | _ -> raise (Modality_failure ("Tried to compare mismatched modalities " ^ show_modality m1 ^ " and " ^ show_modality m2))

let show_mode = function
  | Pointwise -> "pt"
  | Parametric -> "par"

let show_modality = function
  | IdPointwise -> "."
  | IdParametric -> "."
  | Components -> ".components"
  | Discrete -> ".discrete"
  | DiscreteComponents -> ".components.discrete"
