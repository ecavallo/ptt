exception Mode_mismatch

type mode =
  | Pointwise
  | Parametric
[@@deriving show{ with_path = false }, eq]

type modality =
  | Id
  | Components
  | Discrete
  | Global
  | DiscreteComponents
  | DiscreteGlobal
[@@deriving show{ with_path = false }, eq]

let assert_mode m1 m2 =
  if m1 = m2 then () else raise Mode_mismatch

let src m = function
  | Id -> m
  | Components -> assert_mode m Pointwise; Parametric
  | Discrete -> assert_mode m Parametric; Pointwise
  | Global -> assert_mode m Pointwise; Parametric
  | DiscreteComponents -> assert_mode m Parametric; Parametric
  | DiscreteGlobal -> assert_mode m Parametric; Parametric

let dst m = function
  | Id -> m
  | Components -> assert_mode m Parametric; Pointwise
  | Discrete -> assert_mode m Pointwise; Parametric
  | Global -> assert_mode m Parametric; Pointwise
  | DiscreteComponents -> assert_mode m Parametric; Parametric
  | DiscreteGlobal -> assert_mode m Parametric; Parametric

let compose m1 m2 =
  match m1, m2 with
  | Id, _ -> m2
  | _, Id -> m1
  | Components, Discrete -> Id
  | Components, DiscreteComponents -> Components
  | Components, DiscreteGlobal -> Global
  | Discrete, Components -> DiscreteComponents
  | Discrete, Global -> DiscreteGlobal
  | Global, Discrete -> Id
  | Global, DiscreteComponents -> Components
  | Global, DiscreteGlobal -> Global
  | DiscreteComponents, Discrete -> Discrete
  | DiscreteComponents, DiscreteComponents -> DiscreteComponents
  | DiscreteComponents, DiscreteGlobal -> DiscreteGlobal
  | DiscreteGlobal, Discrete -> Discrete
  | DiscreteGlobal, DiscreteComponents -> DiscreteComponents
  | DiscreteGlobal, DiscreteGlobal -> DiscreteGlobal
  | _ -> raise Mode_mismatch

let leq m1 m2 =
  match m1, m2 with
  | Id, Id -> true
  | Id, DiscreteComponents -> true
  | Id, DiscreteGlobal -> false
  | Components, Components -> true
  | Components, Global -> false
  | Discrete, Discrete -> true
  | Global, Components -> true
  | Global, Global -> true
  | DiscreteComponents, Id -> false
  | DiscreteComponents, DiscreteComponents -> true
  | DiscreteComponents, DiscreteGlobal -> false
  | DiscreteGlobal, Id -> true
  | DiscreteGlobal, DiscreteComponents -> true
  | DiscreteGlobal, DiscreteGlobal -> true
  | _ -> raise Mode_mismatch

let show_mode = function
  | Pointwise -> "pt"
  | Parametric -> "par"

let show_modality = function
  | Id -> "."
  | Components -> ".components"
  | Discrete -> ".discrete"
  | Global -> ".global"
  | DiscreteComponents -> ".components.discrete"
  | DiscreteGlobal -> ".global.discrete"
