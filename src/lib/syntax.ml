type idx = int
[@@deriving show{ with_path = false }, eq]

type uni_level = int
[@@deriving show{ with_path = false }, eq]

type bdim =
  | BVar of idx
  | Const of int
[@@deriving eq]

type t =
  | Var of idx (* DeBruijn indices for variables *)
  | Let of t * (* BINDS *) t | Check of t * t
  | Nat | Zero | Suc of t | NRec of (* BINDS *) t * t * (* BINDS 2 *) t * t
  | Pi of t * (* BINDS *) t | Lam of (* BINDS *) t | Ap of t * t
  | Sg of t * (* BINDS *) t | Pair of t * t | Fst of t | Snd of t
  | Id of t * t * t | Refl of t | J of (* BINDS 3 *) t * (* BINDS *) t * t
  | Bridge of (* BBINDS *) t * t list | BApp of t * bdim | BLam of (* BBINDS *) t
  | Extent of bdim * (* BBINDS *) t * (* BBINDS & BINDS *) t * t * (* BINDS *) t list * (* BINDS n & BBINDS *) t
  | Gel of bdim * t list * (* BINDS n *) t | Engel of bdim * t list * t
  | Ungel of int * (* BINDS *) t * (* BBINDS *) t * (* BINDS *) t
  | Uni of uni_level
[@@deriving eq]

exception Indirect_use

let unsubst_bvar i t =
  let bgo depth = function
    | BVar j ->
      if j < depth then BVar j
      else if j = i + depth then BVar depth
      else BVar (j + 1)
    | Const o -> Const o
  in
  let rec go depth = function
    | Var j ->
      if j < depth then Var j
      else if j < i + depth then raise Indirect_use
      else Var (j + 1)
    | Let (def, body) -> Let (go depth def, go (depth + 1) body)
    | Check (term, tp) -> Check (go depth term, go depth tp)
    | Nat -> Nat
    | Zero -> Zero
    | Suc t -> Suc (go depth t)
    | NRec (mot, zero, suc, n) ->
      NRec (go (depth + 1) mot, go depth zero, go (depth + 2) suc, go depth n)
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
    | BApp (t, r) -> BApp (go depth t, bgo depth r)
    | Extent (r, dom, mot, ctx, endcase, varcase) ->
      Extent
        (bgo depth r,
         go (depth + 1) dom,
         go (depth + 2) mot,
         go depth ctx,
         List.map (go (depth + 1)) endcase,
         go (depth + List.length endcase + 2) varcase)
    | Gel (r, ts, t) -> Gel (bgo depth r, List.map (go depth) ts, go (depth + List.length ts) t)
    | Engel (r, ts, t) -> Engel (bgo depth r, List.map (go depth) ts, go depth t)
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

let pp_bdim fmt =
  let open Format in
  function
  | BVar i -> fprintf fmt "#%d" i
  | Const o -> fprintf fmt "%d" o

let rec pp fmt =
  let open Format in
  function
  | Var i -> fprintf fmt "#%d" i
  | Let (def, body) ->
    fprintf fmt "let@,@[<hov>%a@]@,in@,@[<hov%a@]" pp def pp body
  | Check (term, tp) ->
    fprintf fmt "(@[<hov>%a@]@ :@,@[<hov>%a@])" pp term pp tp
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
    fprintf fmt "bapp(@[<hov>@[<hov>%a@],@ @[<hov>%a@]@])" pp t pp_bdim r;
  | Extent (r, dom, mot, ctx, endcase, varcase) ->
    fprintf fmt "extent(@[<hov>@[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])"
     pp_bdim r pp dom pp mot pp ctx pp_list endcase pp varcase;
  | Gel (r, ts, t) ->
    fprintf fmt "Gel(@[<hov>@[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])" pp_bdim r pp_list ts pp t;
  | Engel (r, ts, t) ->
    fprintf fmt "gel(@[<hov>@[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])" pp_bdim r pp_list ts pp t;
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
