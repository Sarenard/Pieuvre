{
  (* prélude du fichier *)
  open Parser
}

(* définitions d'expressions régulières *)
let chiffre = ['0'-'9']
let nombre = chiffre+
let var = ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']*
               
rule token = parse
  | [' ' '\n' '\t']     { token lexbuf }
  | "(*"               { comment 1 lexbuf }

  | "fun"             { FUN }
  | ':'             { COLON }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | "=>"             { BIGARROW }
  | "->"             { SMALLARROW }
  | ','             { COMMA }
  | ":=" {DEFINE}
  | "|" {PIPE}
  
  | "forall" {FORALL}

  | "Type" {TYPE}

  | "Theorem" {THEOREM}
  | "Proof" {PROOF}
  | "Inductive" {INDUCTIVE}

  | "."             { DOT }
  | "Goal"             { GOAL }
  | "intro"             { INTRO }
  | "trivial"             { TRIVIAL }
  | "exact"             { EXACT }
  | "apply"             { APPLY }
  | "Qed"             { QED }

  | var as s { VAR s }
  
  | eof               { EOF }

and comment depth = parse
  | "(*"              { comment (depth + 1) lexbuf }
  | "*)"              {
      if depth = 1 then token lexbuf
      else comment (depth - 1) lexbuf
    }
  | eof               { failwith "Unterminated comment" }
  | _                 { comment depth lexbuf }
