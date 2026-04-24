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
