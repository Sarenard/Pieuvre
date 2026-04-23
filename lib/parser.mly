%{
open Expr
%}

/* PARTIE 2, on liste les lexèmes (lien avec le fichier lexer.mll) ******* */                                   
%token FUN COLON LPAREN RPAREN EOF BIGARROW SMALLARROW GOAL PIPE
/*TACTICS*/
%token INTRO TRIVIAL EXACT DOT QED
/*STATEMENTS*/
%token THEOREM PROOF INDUCTIVE DEFINE
%token <int> INT       /* le lexème INT a un attribut entier */
%token <string> VAR
%token <string> TYPE

/* PARTIE 3, on donne les associativités et on classe les priorités *********** */
/* priorité plus grande sur une ligne située plus bas */
%right SMALLARROW

/* PARTIE 4, les points d'entrée ******************************************* */
%start lambdaterm
%type <Expr.lambdaterm> lambdaterm

%start statements
%type <Expr.statement list> statements

%start tactic_dot
%type <Expr.tactic> tactic_dot

/* PARTIE 5 : STATEMENTS ************************************** */                                                         
%%

statements:
  | l = list(statement) EOF { l }


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
  | t = TYPE {Var t}
  | t1 = term SMALLARROW t2 = term {Pi("_", t1, t2)} 
  (*Termes*)
  | t = VAR {Var t}
  | GOAL LPAREN t = term RPAREN {Goal(0, t)}
  | LPAREN t=lambdaterm RPAREN {t}
  (*Var*)

/* PARTIE 7 : TACTICS ************************************** */                                                         

tactic_dot:
  | t=tactic DOT { t }

tactic:
  | INTRO x=VAR { Intro x }
  | TRIVIAL { Trivial }
  | EXACT t=lambdaterm { Exact(t) }