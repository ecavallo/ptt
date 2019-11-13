type idx = int
[@@deriving show{ with_path = false }, eq]

type uni_level = int
[@@deriving show{ with_path = false }, eq]

type dim =
  | DVar of idx
  | Const of int
[@@deriving eq]

type t =
  | Var of idx (* DeBruijn indices for variables *)
  | Let of t * (* BINDS *) t | Check of t * t
  | Unit | Triv
  | Nat | Zero | Suc of t | NRec of (* BINDS *) t * t * (* BINDS 2 *) t * t
  | Bool | True | False | If of (* BINDS *) t * t * t * t
  | Pi of t * (* BINDS *) t | Lam of (* BINDS *) t | Ap of t * t
  | Sg of t * (* BINDS *) t | Pair of t * t | Fst of t | Snd of t
  | Id of t * t * t | Refl of t | J of (* BINDS 3 *) t * (* BINDS *) t * t
  | Bridge of (* BBINDS *) t * t list | BApp of t * dim | BLam of (* BBINDS *) t
  | Extent of dim * (* BBINDS *) t * (* BBINDS & BINDS *) t * t * (* BINDS *) t list * (* BINDS n & BBINDS *) t
  | Gel of dim * t list * (* BINDS n *) t | Engel of idx * t list * t
  | Ungel of int * (* BINDS *) t * (* BBINDS *) t * (* BINDS *) t
  | Uni of uni_level
[@@deriving eq]

exception Indirect_use

let unsubst_bvar i t =
  let go_dvar depth j =
      if j < depth then j
      else if j = i + depth then depth
      else j + 1
  in
  let go_dim depth = function
    | DVar j -> DVar (go_dvar depth j)
    | Const o -> Const o
  in
  let rec go depth = function
    | Var j ->
      if j < depth then Var j
      else if j < i + depth then raise Indirect_use
      else Var (j + 1)
    | Let (def, body) -> Let (go depth def, go (depth + 1) body)
    | Check (term, tp) -> Check (go depth term, go depth tp)
    | Unit -> Unit
    | Triv -> Triv
    | Nat -> Nat
    | Zero -> Zero
    | Suc t -> Suc (go depth t)
    | NRec (mot, zero, suc, n) ->
      NRec (go (depth + 1) mot, go depth zero, go (depth + 2) suc, go depth n)
    | Bool -> Bool
    | True -> True
    | False -> False
    | If (mot, tt, ff, b) ->
      If (go (depth + 1) mot, go depth tt, go depth ff, go depth b)
    | Pi (l, r) -> Pi (go depth l, go (depth + 1) r)
    | Lam body -> Lam (go (depth + 1) body)
    | Ap (l, r) -> Ap (go depth l, go depth r)
    | Sg (l, r) -> Sg (go depth l, go (depth + 1) r)
    | Fst body -> Fst (go depth body)
    | Snd body -> Snd (go depth body)
    | Pair (l, r) -> Pair (go depth l, go depth r)
    | Id (tp, l, r) -> Id (go depth tp, go depth l, go depth r)
    | Refl t -> Refl (go depth t)
    | J (mot, refl, eq) ->
      J (go (depth + 3) mot, go (depth + 1) refl, go depth eq)
    | Bridge (t, ts) -> Bridge (go (depth + 1) t, List.map (go depth) ts)
    | BLam t -> BLam (go (depth + 1) t)
    | BApp (t, r) -> BApp (go depth t, go_dim depth r)
    | Extent (r, dom, mot, ctx, endcase, varcase) ->
      Extent
        (go_dim depth r,
         go (depth + 1) dom,
         go (depth + 2) mot,
         go depth ctx,
         List.map (go (depth + 1)) endcase,
         go (depth + List.length endcase + 2) varcase)
    | Gel (r, ts, t) -> Gel (go_dim depth r, List.map (go depth) ts, go (depth + List.length ts) t)
    | Engel (i, ts, t) -> Engel (go_dvar depth i, List.map (go depth) ts, go depth t)
    | Ungel (width, mot, gel, case) ->
      Ungel (width, go (depth + 1) mot, go (depth + 1) gel, go (depth + 1) case)
    | Uni j -> Uni j
  in
  try
    Some (go 0 t)
  with
    Indirect_use -> None

let rec condense = function
  | Zero -> Some 0
  | Suc t ->
    begin
      match condense t with
      | Some n -> Some (n + 1)
      | None -> None
    end
  | _ -> None

let pp_dim fmt =
  let open Format in
  function
  | DVar i -> fprintf fmt "#%d" i
  | Const o -> fprintf fmt "%d" o

let rec pp fmt =
  let open Format in
  function
  | Var i -> fprintf fmt "#%d" i
  | Let (def, body) ->
    fprintf fmt "let@,@[<hov>%a@]@,in@,@[<hov%a@]" pp def pp body
  | Check (term, tp) ->
    fprintf fmt "(@[<hov>%a@]@ :@,@[<hov>%a@])" pp term pp tp
  | Unit -> fprintf fmt "unit"
  | Triv -> fprintf fmt "triv"
  | Nat -> fprintf fmt "nat"
  | Zero -> fprintf fmt "0"
  | Suc t ->
    begin
      match condense t with
      | Some n ->
        fprintf fmt "%d" (n + 1)
      | None ->
        fprintf fmt "suc(@[<hov>%a@])" pp t
    end
  | NRec (mot, zero, suc, n) ->
    fprintf fmt "rec(@[<hov>@[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])"
      pp mot pp zero pp suc pp n;
  | Bool -> fprintf fmt "bool"
  | True -> fprintf fmt "true"
  | False -> fprintf fmt "false"
  | If (mot, tt, ff, b) ->
    fprintf fmt "if(@[<hov>@[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])"
      pp mot pp tt pp ff pp b;
  | Pi (l, r) ->
    fprintf fmt "Pi(@[<hov>@[<hov>%a@],@ @[<hov>%a@]@])" pp l pp r;
  | Lam body ->
    fprintf fmt "lam(@[<hov>%a@])" pp body
  | Ap (l, r) ->
    fprintf fmt "app(@[<hov>@[<hov>%a@],@ @[<hov>%a@]@])" pp l pp r
  | Sg (l, r) ->
    fprintf fmt "Sg(@[<hov>@[<hov>%a@],@ @[<hov>%a@]@])" pp l pp r
  | Fst body ->
    fprintf fmt "fst(@[<hov>%a@])" pp body
  | Snd body ->
    fprintf fmt "snd(@[<hov>%a@])" pp body
  | Pair (l, r) ->
    fprintf fmt "pair(@[<hov>@[<hov>%a@],@ @[<hov>%a@]@])" pp l pp r
  | Id (tp, l, r) ->
    fprintf fmt "Id(@[<hov>@[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])" pp tp pp l pp r;
  | Refl t ->
    fprintf fmt "refl(@[<hov>%a@])" pp t
  | J (mot, refl, eq) ->
    fprintf fmt "J(@[<hov>@[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])" pp mot pp refl pp eq;
  | Bridge (t, ts) ->
    fprintf fmt "Bridge(@[<hov>@[<hov>%a@],@ @[<hov>%a@]@])"
      pp t pp_list ts;
  | BLam t ->
    fprintf fmt "blam(@[<hov>%a@])" pp t;
  | BApp (t, r) ->
    fprintf fmt "bapp(@[<hov>@[<hov>%a@],@ @[<hov>%a@]@])" pp t pp_dim r;
  | Extent (r, dom, mot, ctx, endcase, varcase) ->
    fprintf fmt "extent(@[<hov>@[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])"
     pp_dim r pp dom pp mot pp ctx pp_list endcase pp varcase;
  | Gel (r, ts, t) ->
    fprintf fmt "Gel(@[<hov>@[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])" pp_dim r pp_list ts pp t;
  | Engel (i, ts, t) ->
    fprintf fmt "gel(@[<hov>@[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])" pp_dim (DVar i) pp_list ts pp t;
  | Ungel (width, mot, gel, case) ->
    fprintf fmt "ungel(@[<hov>@[<hov>%d@],@ @[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])" width pp mot pp gel pp case
  | Uni i -> fprintf fmt "U<%d>" i

and pp_list fmt =
  Format.fprintf fmt "[%a]" (Format.pp_print_list ~pp_sep:(fun fmt _ -> Format.fprintf fmt "; ") pp)

let show t =
  let b = Buffer.create 100 in
  let fmt = Format.formatter_of_buffer b in
  pp fmt t;
  Format.pp_print_flush fmt ();
  Buffer.contents b
