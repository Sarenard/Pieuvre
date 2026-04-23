{
  (* prélude du fichier *)
  open Parser
          
}

(* définitions d'expressions régulières *)
let chiffre = ['0'-'9']
let nombre = chiffre+
let var = ['a'-'z']['a'-'z']*['0'-'9']*
let type = ['A'-'Z']['A'-'Z']*['0'-'9']*
               
rule token = parse
  | [' ' '\n' '\t']     { token lexbuf }

  | "fun"             { FUN }
  | ':'             { COLON }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | "=>"             { BIGARROW }
  | "->"             { SMALLARROW }

  | "."             { DOT }
  | "Goal"             { GOAL }
  | "intro"             { INTRO }
  | "trivial"             { TRIVIAL }
  | "exact"             { EXACT }
  | "Qed"             { QED }

  | var as s { VAR s }
  | type as s { TYPE s }
  
  | eof               { EOF }