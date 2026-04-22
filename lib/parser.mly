%{
open Expr
%}

/* PARTIE 2, on liste les lexèmes (lien avec le fichier lexer.mll) ******* */                                   
%token FUN COLON LPAREN RPAREN EOF BIGARROW SMALLARROW GOAL
/*TACTICS*/
%token INTRO TRIVIAL
%token <int> INT       /* le lexème INT a un attribut entier */
%token <string> VAR
%token <string> TYPE

/* PARTIE 3, on donne les associativités et on classe les priorités *********** */
/* priorité plus grande sur une ligne située plus bas */
%left SMALLARROW

/* PARTIE 4, le point d'entrée ******************************************* */
%start main
%type <Expr.lambdaterm> main

%start tactic_main
%type <Expr.tactic> tactic_main

/* PARTIE 5 : Les Termes ************************************** */                                                         
%%

main:
  | e=expression EOF { e }

expression:
  | FUN LPAREN x=VAR COLON t=term RPAREN BIGARROW e=expression {Func(x, t, e)}
  | applic { $1 }

applic:
  | e1=applic e2=term {App(e1, e2)}
  | term { $1 }

term:
  (*Types*)
  | t = TYPE {Var t}
  | t1 = term SMALLARROW t2 = term {Pi("_", t1, t2)} 
  (*Termes*)
  | t = VAR {Var t}
  | GOAL LPAREN t = term RPAREN {Goal(0, t)}
  (*Var*)

/* PARTIE 6 : Les tactiques ************************************** */                                                         

tactic_main:
  | t=tactic EOF { t }

tactic:
  | INTRO x=VAR { Intro x }
  | TRIVIAL { Trivial }