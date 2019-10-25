%{
  open Concrete_syntax
%}

%token <int> NUMERAL
%token <string> ATOM
%token COLON SEMI PIPE AT COMMA RIGHT_ARROW UNDERSCORE
%token LPR RPR LANGLE RANGLE LBR RBR LCU RCU
%token EQUALS
%token TIMES FST SND
%token LAM LET IN END WITH OF DEF
%token BRI ATSIGN EXTENT
%token GEL ENGEL UNGEL
%token REC SUC NAT ZERO
%token IF TRUE FALSE BOOL
%token UNIV
%token QUIT NORMALIZE
%token ID REFL MATCH
%token EOF

%start <Concrete_syntax.signature> sign
%%

name:
  | s = ATOM
    { s }
  | UNDERSCORE
    { "_" }

decl:
  | LET; nm = name; COLON; tp = term; EQUALS; body = term
    { Def {name = nm; def = body; tp} }
  | QUIT { Quit }
  | NORMALIZE; DEF; a = name
    { NormalizeDef a  }
  | NORMALIZE; tm = term; AT; tp = term { NormalizeTerm {term = tm; tp} };

sign:
  | EOF { [] }
  | d = decl; s = sign { d :: s };

bdim:
  | r = name { BVar r }
  | n = NUMERAL { Const n };

endpoints:
  | LCU; endpoints = separated_list(SEMI, term); RCU { endpoints }

atomic:
  | LPR; t = term; RPR
    { t }
  | a = name
    { Var a }
  | ZERO
    { Lit 0 }
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
  | LBR; name = name; RBR; body = term; endpoints = endpoints
    { Bridge(Binder {name; body}, endpoints) }

spine:
  | t = atomic { Term t }
  | ATSIGN; b = bdim { BDim b };

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
  | SUC; t = term { Suc t }
  | REC; n = term; AT; mot_name = name; RIGHT_ARROW; mot = term; WITH;
    PIPE; ZERO; RIGHT_ARROW; zero_case = term;
    PIPE; SUC; suc_var = name; COMMA; ih_var = name; RIGHT_ARROW; suc_case = term
    { NRec {
        mot = Binder {name = mot_name; body = mot};
        zero = zero_case;
        suc = Binder2 {name1 = suc_var; name2 = ih_var; body = suc_case};
        nat = n
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
  | EXTENT; bdim = bdim; OF; ctx = term;
    IN; dom_dim = name; RIGHT_ARROW; dom = term;
    AT; mot_dim = name; mot_var = name; RIGHT_ARROW; mot = term;
    WITH; PIPE;
    cases = extent_cases
    { let (endcase, varcase) = cases in
      Extent
        {bdim;
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
  | FST; t = term { Fst t }
  | SND; t = term { Snd t }
  | GEL; bdim = bdim; endpoints = endpoints; LPR; names = nonempty_list(name); RIGHT_ARROW; body = term; RPR
    { Gel (bdim, endpoints, BinderN {names; body}) }
  | GEL; bdim = bdim; body = atomic
    { Gel (bdim, [], BinderN {names = []; body}) }
  | ENGEL; bdim = bdim; endpoints = endpoints; t = atomic
    { Engel (bdim, endpoints, t) }
  | ENGEL; bdim = bdim; t = atomic
    { Engel (bdim, [], t) }
  | UNGEL; gel_name = name; COLON; width = NUMERAL; RIGHT_ARROW; gel_body = term; AT;
    mot_name = name; RIGHT_ARROW; mot_body = term; WITH
    PIPE; ENGEL; case_name = name; RIGHT_ARROW; case_body = term;
    { Ungel
        {width;
         mot = Binder {name = mot_name; body = mot_body};
         gel = Binder {name = gel_name; body = gel_body};
         case = Binder {name = case_name; body = case_body}} }
  
tele_cell:
  | LPR name = name; COLON ty = term; RPR
    { Cell {name; ty} }
; 
