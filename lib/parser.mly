%{
open Expr
%}

/* PARTIE 2, on liste les lexèmes (lien avec le fichier lexer.mll) ******* */                                   
%token FUN COLON LPAREN RPAREN EOF BIGARROW SMALLARROW GOAL
/*TACTICS*/
%token INTRO TRIVIAL EXACT DOT QED
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
  | e=lambdaterm EOF { e }

lambdaterm:
  | FUN LPAREN x=VAR COLON t=term RPAREN BIGARROW e=lambdaterm {Func(x, t, e)}
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
  | GOAL LPAREN t = term RPAREN DOT {Goal(0, t)}
  | LPAREN t=lambdaterm RPAREN {t}
  (*Var*)

/* PARTIE 6 : Les tactiques ************************************** */                                                         

tactic_main:
  | t=tactic DOT { t }

tactic:
  | INTRO x=VAR { Intro x }
  | TRIVIAL { Trivial }
  | QED { Qed }
  | EXACT t=lambdaterm { Exact(t) }