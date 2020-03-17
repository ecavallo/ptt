%{
  open Concrete_syntax
%}

%token <int> NUMERAL
%token <string> ATOM
%token COLON SEMI PIPE AT COMMA RIGHT_ARROW UNDERSCORE
%token LPR RPR LANGLE RANGLE LBR RBR LCU RCU
%token EQUALS
%token TIMES FST SND
%token LAM LET IN END WITH OF DEF POSTULATE
%token BRI ATSIGN EXTENT
%token GEL ENGEL UNGEL
%token GLOBAL ENGLOBE UNGLOBE
%token CODISC ENCODISC UNCODISC
%token UNIT TRIV
%token REC SUC NAT ZERO
%token LIST NIL CONS LISTREC
%token IF TRUE FALSE BOOL
%token UNIV
%token QUIT NORMALIZE
%token ID REFL MATCH
%token PAR PT
%token EOF

%start <Concrete_syntax.signature> sign
%%

name:
  | s = ATOM
    { s }
  | UNDERSCORE
    { "_" }

mode:
  | { Check.Parametric }
  | PAR { Check.Parametric }
  | PT { Check.Pointwise }
    
decl:
  | LET; mode = mode; nm = name; COLON; tp = term; EQUALS; body = term
    { Def {mode; name = nm; def = body; tp} }
  | POSTULATE; mode = mode; nm = name; COLON; tp = term
    { Postulate {mode; name = nm; tp} }
  | QUIT { Quit }
  | NORMALIZE; DEF; a = name
    { NormalizeDef a  }
  | NORMALIZE; mode = mode; tm = term; AT; tp = term { NormalizeTerm {mode; term = tm; tp} };

sign:
  | EOF { [] }
  | d = decl; s = sign { d :: s };

dim:
  | r = name { DVar r }
  | n = NUMERAL { Const n };

endpoints:
  | LCU; endpoints = separated_list(SEMI, term); RCU { endpoints };

term_option:
  | t = term { Some t }
  | TIMES { None };

endpoint_options:
  | LCU; endpoints = separated_list(SEMI, term_option); RCU { endpoints };

atomic:
  | LPR; t = term; RPR
    { t }
  | a = name
    { Var a }
  | UNIT
    { Unit }
  | TRIV
    { Triv }
  | ZERO
    { Lit 0 }
  | NIL
    { Nil }
  | TRUE
    { True }
  | FALSE
    { False }
  | n = NUMERAL
    { Lit n }
  | UNIV; LANGLE; i = NUMERAL; RANGLE
    { Uni i }
  | NAT { Nat }
  | BOOL { Bool }
  | LANGLE left = term; COMMA; right = term; RANGLE
    { Pair (left, right) }
  | LBR; name = name; RBR; body = term; endpoints = endpoint_options
    { Bridge(Binder {name; body}, endpoints) }
  | FST; t = atomic { Fst t }
  | SND; t = atomic { Snd t }

spine:
  | t = atomic { Term t }
  | ATSIGN; b = dim { Dim b };

extent_cases:
  | name = name; RIGHT_ARROW; body = term; PIPE; ext = extent_cases
    { let (endcases, varcase) = ext in (Binder {name; body} :: endcases, varcase) }
  | name = name; names = nonempty_list(name); RIGHT_ARROW; varcase = term;
    { ([], BinderN {names = name :: names; body = varcase}) };

term:
  | f = atomic; args = list(spine)
    { Ap (f, args) }
  | LET; name = name; COLON; tp = term; EQUALS; def = term; IN; body = term
    { Let (Check {term = def; tp}, Binder {name; body}) }
  | LET; name = name; EQUALS; def = term; IN; body = term; END
    { Let (def, Binder {name; body}) }
  | LPR t = term; AT; tp = term RPR
    { Check {term = t; tp} }
  | SUC; t = atomic { Suc t }
  | REC; n = term; AT; mot_name = name; RIGHT_ARROW; mot = term; WITH;
    PIPE; ZERO; RIGHT_ARROW; zero_case = term;
    PIPE; SUC; suc_var = name; COMMA; ih_var = name; RIGHT_ARROW; suc_case = term
    { NRec {
        mot = Binder {name = mot_name; body = mot};
        zero = zero_case;
        suc = Binder2 {name1 = suc_var; name2 = ih_var; body = suc_case};
        nat = n
        } }
  | LIST; t = atomic { List t }
  | CONS; a = atomic; t = atomic { Cons (a, t) }
  | LISTREC; l = term; AT; mot_name = name; RIGHT_ARROW; mot = term; WITH;
    PIPE; NIL; RIGHT_ARROW; nil_case = term;
    PIPE; CONS; a_var = name; t_var = name; COMMA; ih_var = name; RIGHT_ARROW; cons_case = term
    { ListRec {
        mot = Binder {name = mot_name; body = mot};
        nil = nil_case;
        cons = Binder3 {name1 = a_var; name2 = t_var; name3 = ih_var; body = cons_case};
        list = l
        } }
  | IF; b = term; AT; mot_name = name; RIGHT_ARROW; mot = term; WITH;
    PIPE; TRUE; RIGHT_ARROW; true_case = term;
    PIPE; FALSE; RIGHT_ARROW; false_case = term;
    { If {
        mot = Binder {name = mot_name; body = mot};
        tt = true_case;
        ff = false_case;
        bool = b
      } }
  | ID; tp = atomic; left = atomic; right = atomic
    { Id (tp, left, right) }
  | REFL; t = atomic
    { Refl t }
  | MATCH; eq = term; AT; name1 = name; name2 = name; name3 = name; RIGHT_ARROW; mot_term = term; WITH
    PIPE; REFL; name = name; RIGHT_ARROW; refl = term;
    { J {mot = Binder3 {name1; name2; name3; body = mot_term}; refl = Binder {name; body = refl}; eq} }
  | EXTENT; dim = dim; OF; ctx = term;
    IN; dom_dim = name; RIGHT_ARROW; dom = term;
    AT; mot_dim = name; mot_var = name; RIGHT_ARROW; mot = term;
    WITH; PIPE;
    cases = extent_cases
    { let (endcase, varcase) = cases in
      Extent
        {dim;
         dom = Binder {name = dom_dim; body = dom};
         mot = Binder2 {name1 = mot_dim; name2 = mot_var; body = mot};
         ctx;
         endcase;
         varcase} }
  | LAM; names = nonempty_list(name); RIGHT_ARROW; body = term
    { Lam (BinderN {names; body}) }
  | BRI; names = nonempty_list(name); RIGHT_ARROW; body = term
    { BLam (BinderN {names; body}) }
  | tele = nonempty_list(tele_cell); RIGHT_ARROW; cod = term
    { Pi (tele, cod) }
  | tele = nonempty_list(tele_cell); TIMES; cod = term
    { Sg (tele, cod) }
  | dom = atomic RIGHT_ARROW; cod = term
    { Pi ([Cell {name = ""; ty = dom}], cod)}
  | dom = atomic; TIMES; cod = term
    { Sg ([Cell {name = ""; ty = dom}], cod)}
  | GEL; dim = dim; endpoints = endpoints; LPR; names = nonempty_list(name); RIGHT_ARROW; body = term; RPR
    { Gel (dim, endpoints, BinderN {names; body}) }
  | GEL; dim = dim; body = atomic
    { Gel (dim, [], BinderN {names = []; body}) }
  | ENGEL; name = name; endpoints = endpoints; t = atomic
    { Engel (name, endpoints, t) }
  | ENGEL; name = name; t = atomic
    { Engel (name, [], t) }
  | UNGEL; gel_name = name; COLON; width = NUMERAL; RIGHT_ARROW; gel_body = term; AT;
    mot_name = name; RIGHT_ARROW; mot_body = term; WITH
    PIPE; ENGEL; case_name = name; RIGHT_ARROW; case_body = term;
    { Ungel
        {width;
         mot = Binder {name = mot_name; body = mot_body};
         gel = Binder {name = gel_name; body = gel_body};
         case = Binder {name = case_name; body = case_body}} }
  | CODISC; t = atomic { Codisc t }
  | ENCODISC; t = atomic { Encodisc t }
  | UNCODISC; t = atomic { Uncodisc t }
  | GLOBAL; t = atomic { Global t }
  | ENGLOBE; t = atomic { Englobe t }
  | UNGLOBE; t = atomic { Unglobe t }
  
tele_cell:
  | LPR name = name; COLON ty = term; RPR
    { Cell {name; ty} }
; 
