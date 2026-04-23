%{
  open Expr
%}

/* PARTIE 2, on liste les lexèmes (lien avec le fichier lexer.mll) ******* */                                   
%token FUN COLON LPAREN RPAREN EOF BIGARROW SMALLARROW GOAL PIPE TYPE
/*TACTICS*/
%token INTRO TRIVIAL EXACT DOT QED APPLY
/*STATEMENTS*/
%token THEOREM PROOF INDUCTIVE DEFINE
%token <int> INT       /* le lexème INT a un attribut entier */
%token <string> VAR

/* PARTIE 3, on donne les associativités et on classe les priorités *********** */
/* priorité plus grande sur une ligne située plus bas */
%right SMALLARROW

/* PARTIE 4, les points d'entrée ******************************************* */
%start main_term
%type <Expr.lambdaterm> main_term

%start main_statements
%type <Expr.statement list> main_statements

%start main_tactic
%type <Expr.tactic> main_tactic

%%

main_term:
  | t = lambdaterm EOF { t }

main_statements:
  | l = list(statement) EOF { l }

main_tactic:
  | t = tactic_dot EOF { t }

/* PARTIE 5 : STATEMENTS ************************************** */                                                         

statement: 
  | THEOREM name=VAR COLON t=lambdaterm DOT {Theorem(name, t)}
  | PROOF DOT l=list(tactic_dot) QED DOT {Proof(l)}
  (*
  Inductive statements are of the form
  Inductive name : arity :=
    [
      | name : pos_type
    ]
  .
  by https://link.springer.com/content/pdf/10.1007/BFb0037116.pdf
  *)
  | INDUCTIVE name=VAR COLON arity=lambdaterm DEFINE cons=list(constructor) DOT {Inductive(name, arity, cons)}

constructor:
  | PIPE name=VAR COLON ty=lambdaterm {Constructor(name, ty)} 

/* PARTIE 6 : TERMS ************************************** */                                                         

lambdaterm:
  | FUN LPAREN x=VAR COLON t=term RPAREN BIGARROW e=lambdaterm {Func(x, t, e)}
  | applic { $1 }

applic:
  | e1=applic e2=term {App(e1, e2)}
  | term { $1 }

term:
  (*Types*)
  | TYPE {Type}
  | t1 = term SMALLARROW t2 = term {Pi("_", t1, t2)} 
  (*Termes*)
  | t = VAR {Var t}
  | GOAL LPAREN t = term RPAREN {Goal(0, t)}
  | LPAREN t=lambdaterm RPAREN {t}
  (*Var*)

/* PARTIE 7 : TACTICS ************************************** */                                                         

tactic_dot:
  | tactic DOT { $1 }

tactic:
  | INTRO x=VAR { Intro(x) }
  | TRIVIAL { Trivial }
  | APPLY x=VAR { Apply(x) }
  | EXACT t=lambdaterm { Exact(t) }