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
  | List of t | Nil | Cons of t * t | ListRec of (* BINDS *) t * t * (* BINDS 3 *) t * t
  | Bool | True | False | If of (* BINDS *) t * t * t * t
  | Coprod of t * t | Inl of t | Inr of t | Case of (* BINDS *) t * (* BINDS *) t * (* BINDS *) t * t
  | Void | Abort of (* BINDS *) t * t
  | Pi of t * (* BINDS *) t | Lam of (* BINDS *) t | Ap of t * t
  | Sg of t * (* BINDS *) t | Pair of t * t | Fst of t | Snd of t
  | Id of t * t * t | Refl of t | J of (* BINDS 3 *) t * (* BINDS *) t * t
  | Bridge of (* BBINDS *) t * t option list | BApp of t * dim | BLam of (* BBINDS *) t
  | Extent of dim * (* BBINDS *) t * (* BBINDS & BINDS *) t * t * (* BINDS *) t list * (* BINDS n & BBINDS *) t
  | Gel of dim * t list * (* BINDS n *) t | Engel of idx * t list * t
  | Ungel of int * (* BINDS *) t * (* BBINDS *) t * (* BINDS *) t
  | Codisc of t | Encodisc of t | Uncodisc of t
  | Global of t | Englobe of t | Unglobe of t
  | Disc of t | Endisc of t | Letdisc of Mode.modality * (* BINDS *) t * (* BINDS *) t * t
  | Letdiscbridge of Mode.modality * int * (* BINDS *) t * (* BINDS *) t * (* BBINDS *) t
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
    | List t -> List (go depth t)
    | Nil -> Nil
    | Cons (a, t) -> Cons (go depth a, go depth t)
    | ListRec (mot, nil, cons, l) ->
      ListRec (go (depth + 1) mot, go depth nil, go (depth + 3) cons, go depth l)
    | Bool -> Bool
    | True -> True
    | False -> False
    | If (mot, tt, ff, b) ->
      If (go (depth + 1) mot, go depth tt, go depth ff, go depth b)
    | Coprod (t1, t2) -> Coprod (go depth t1, go depth t2)
    | Inl t -> Inl (go depth t)
    | Inr t -> Inr (go depth t)
    | Case (mot, inl, inr, co) ->
      Case (go (depth + 1) mot, go (depth + 1) inl, go (depth + 1) inr, go depth co)
    | Void -> Void
    | Abort (mot, vd) -> Abort (go (depth + 1) mot, go depth vd)
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
    | Bridge (t, ts) -> Bridge (go (depth + 1) t, List.map (Option.map (go depth)) ts)
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
    | Global t -> Global (go depth t)
    | Englobe t -> Englobe (go depth t)
    | Unglobe t -> Unglobe (go depth t)
    | Codisc t -> Codisc (go depth t)
    | Encodisc t -> Encodisc (go depth t)
    | Uncodisc t -> Uncodisc (go depth t)
    | Disc t -> Disc (go depth t)
    | Endisc t -> Endisc (go depth t)
    | Letdisc (m, mot, case, d) -> Letdisc (m, go (depth + 1) mot, go (depth + 1) case, go depth d)
    | Letdiscbridge (m, width, mot, case, d) -> Letdiscbridge (m, width, go (depth + 1) mot, go (depth + 1) case, go (depth + 1) d)
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

let pp_option pp fmt =
  function
  | None -> Format.fprintf fmt "*"
  | Some a -> pp fmt a

let pp_list pp fmt =
  Format.fprintf fmt "[%a]" (Format.pp_print_list ~pp_sep:(fun fmt _ -> Format.fprintf fmt "; ") pp)

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
  | List t -> fprintf fmt "list(@[<hov>%a@])" pp t
  | Nil -> fprintf fmt "nil"
  | Cons (a, t) -> fprintf fmt "cons(@[<hov>@[<hov>%a@],@ @[<hov>%a@]@])" pp a pp t
  | ListRec (mot, nil, cons, l) ->
    fprintf fmt "listrec(@[<hov>@[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])"
      pp mot pp nil pp cons pp l;
  | Bool -> fprintf fmt "bool"
  | True -> fprintf fmt "true"
  | False -> fprintf fmt "false"
  | If (mot, tt, ff, b) ->
    fprintf fmt "if(@[<hov>@[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])"
      pp mot pp tt pp ff pp b;
  | Coprod (t1, t2) -> fprintf fmt "coprod(@[<hov>@[<hov>%a@],@ @[<hov>%a@]@])" pp t1 pp t2
  | Inl t -> fprintf fmt "inl(@[<hov>%a@])" pp t
  | Inr t -> fprintf fmt "inr(@[<hov>%a@])" pp t
  | Case (mot, inl, inr, co) ->
    fprintf fmt "case(@[<hov>@[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])"
      pp mot pp inl pp inr pp co;
  | Void -> fprintf fmt "void"
  | Abort (mot, vd) ->
    fprintf fmt "abort(@[<hov>@[<hov>%a@],@ @[<hov>%a@]@])" pp mot pp vd;
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
      pp t (pp_list (pp_option pp)) ts;
  | BLam t ->
    fprintf fmt "blam(@[<hov>%a@])" pp t;
  | BApp (t, r) ->
    fprintf fmt "bapp(@[<hov>@[<hov>%a@],@ @[<hov>%a@]@])" pp t pp_dim r;
  | Extent (r, dom, mot, ctx, endcase, varcase) ->
    fprintf fmt "extent(@[<hov>@[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])"
     pp_dim r pp dom pp mot pp ctx (pp_list pp) endcase pp varcase;
  | Gel (r, ts, t) ->
    fprintf fmt "Gel(@[<hov>@[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])" pp_dim r (pp_list pp) ts pp t;
  | Engel (i, ts, t) ->
    fprintf fmt "gel(@[<hov>@[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])" pp_dim (DVar i) (pp_list pp) ts pp t;
  | Ungel (width, mot, gel, case) ->
    fprintf fmt "ungel(@[<hov>@[<hov>%d@],@ @[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])" width pp mot pp gel pp case
  | Global t ->
    fprintf fmt "Global(@[<hov>%a@])" pp t
  | Englobe t ->
    fprintf fmt "englobe(@[<hov>%a@])" pp t
  | Unglobe t ->
    fprintf fmt "unglobe(@[<hov>%a@])" pp t
  | Codisc t ->
    fprintf fmt "Codisc(@[<hov>%a@])" pp t
  | Encodisc t ->
    fprintf fmt "encodisc(@[<hov>%a@])" pp t
  | Uncodisc t ->
    fprintf fmt "uncodisc(@[<hov>%a@])" pp t
  | Disc t ->
    fprintf fmt "Disc(@[<hov>%a@])" pp t
  | Endisc t ->
    fprintf fmt "endisc(@[<hov>%a@])" pp t
  | Letdisc (m, mot, case, d) ->
    fprintf fmt "letdisc(@[<hov>@[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])"
      Mode.pp_modality m pp mot pp case pp d
  | Letdiscbridge (m, width, mot, case, d) ->
    fprintf fmt "letdisc(@[<hov>@[<hov>%a@],@ @[<hov>%d@],@ @[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])"
      Mode.pp_modality m width pp mot pp case pp d
  | Uni i -> fprintf fmt "U<%d>" i

let show t =
  let b = Buffer.create 100 in
  let fmt = Format.formatter_of_buffer b in
  pp fmt t;
  Format.pp_print_flush fmt ();
  Buffer.contents b
