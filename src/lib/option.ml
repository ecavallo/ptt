let some a = Some a

let map f =
  function
  | Some a -> Some (f a)
  | None -> None

let fold d f =
  function
  | Some a -> f a
  | None -> d
