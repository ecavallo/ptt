{
open Lexing
open Grammar

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }

let make_table num elems =
  let table = Hashtbl.create num in
  List.iter (fun (k, v) -> Hashtbl.add table k v) elems;
  table

let keywords =
  make_table 0 [
    ("unit", UNIT);
    ("triv", TRIV);
    ("nat", NAT);
    ("zero", ZERO);
    ("suc", SUC);
    ("list", LIST);
    ("nil", NIL);
    ("cons", CONS);
    ("listrec", LISTREC);
    ("bool", BOOL);
    ("tt", TRUE);
    ("ff", FALSE);
    ("inl", INL);
    ("inr", INR);
    ("case", CASE);
    ("void", VOID);
    ("abort", ABORT);
    ("let", LET);
    ("in", IN);
    ("with", WITH);
    ("if", IF);
    ("rec", REC);
    ("fst", FST);
    ("snd", SND);
    ("fun", LAM);
    ("bri", BRI);
    ("U", UNIV);
    ("match", MATCH);
    ("Id", ID);
    ("refl", REFL);
    ("extent", EXTENT);
    ("Gel", GEL);
    ("gel", ENGEL);
    ("ungel", UNGEL);
    ("Codisc", CODISC);
    ("codisc", ENCODISC);
    ("uncodisc", UNCODISC);
    ("Global", GLOBAL);
    ("glob", ENGLOBE);
    ("unglob", UNGLOBE);
    ("Disc", DISC);
    ("disc", ENDISC);
    ("undisc", UNDISC);
    ("at", AT);
    ("of", OF);
    ("def", DEF);
    ("postulate", POSTULATE);
    ("normalize", NORMALIZE);
    ("par", PAR);
    ("pt", PT);
    ("cmp", CMP);
    ("glb", GLB);
    ("dsc", DSC);
    ("quit", QUIT);
  ]
}

let number = ['0'-'9']['0'-'9']*
let whitespace = [' ' '\t']+
let line_ending = '\r' | '\n' | "\r\n"
let atom_first = ['a'-'z' 'A'-'Z' '_']
let atom_next = ['a'-'z' 'A'-'Z' '_' '-' '*' '/' '0'-'9' '\'']
let atom = atom_first atom_next*

rule token = parse
  | number
    { (NUMERAL (int_of_string (Lexing.lexeme lexbuf))) }
  | '('
    { LPR }
  | ')'
    { RPR }
  | '|'
    { PIPE }
  | '.'
    { DOT }
  | ','
    { COMMA }
  | '*'
    { TIMES }
  | "×"
    { TIMES }
  | "+"
    { PLUS }
  | ':'
    { COLON }
  | ';'
    { SEMI }
  | "="
    { EQUALS }
  | "->"
    { RIGHT_ARROW }
  | "<"
    { LANGLE }
  | ">"
    { RANGLE }
  | "["
    { LBR }
  | "]"
    { RBR }
  | "{"
    { LCU }
  | "}"
    { RCU }
  | "λ"
    { LAM }
  | '_'
    { UNDERSCORE }
  | '@'
    { ATSIGN }
  | "--"
    { comment lexbuf }
  | line_ending
    { new_line lexbuf; token lexbuf }
  | whitespace
    { token lexbuf }
  | eof
    { EOF }
  | atom
    {
      let input = lexeme lexbuf in
      begin try
        let kwd = Hashtbl.find keywords input in
        kwd
      with Not_found ->
        (Grammar.ATOM input)
      end
    }
  | _
    { Printf.eprintf "Unexpected char: %s" (lexeme lexbuf); token lexbuf }
and comment = parse
  | line_ending
    { new_line lexbuf; token lexbuf }
  | _
    { comment lexbuf }
