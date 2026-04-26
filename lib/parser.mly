%{
  open Expr
%}

(*
TODO : some error recovery / indications
*)

/* PART 1 : LEXEMES ******* */                                   
/*GENERAL*/
%token FUN COLON LPAREN RPAREN EOF BIGARROW SMALLARROW GOAL PIPE TYPE FORALL COMMA
/*TACTICS*/
%token INTRO TRIVIAL EXACT DOT QED APPLY
/*STATEMENTS*/
%token THEOREM PROOF INDUCTIVE DEFINE
%token <int> INT       /* le lexème INT a un attribut entier */
%token <string> VAR

/* PART 2, PRIORITIES *********** */
/* (higher = smaller priority) */

/* PART 3, ACCESS POINTS ******************************************* */
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

/* PART 4 : STATEMENTS ************************************** */                                                         

statement: 
  | THEOREM name=VAR COLON t=lambdaterm DOT {STheorem(name, t)}
  | PROOF DOT l=list(tactic_dot) QED DOT {SProof(l)}
  (*
  Inductive statements are of the form
  Inductive name : arity :=
    [
      | name : pos_type
    ]
  .
  by https://link.springer.com/content/pdf/10.1007/BFb0037116.pdf
  *)
  | INDUCTIVE name=VAR COLON arity=lambdaterm DEFINE cons=list(constructor) DOT {SInductive(name, arity, cons)}

constructor:
  | PIPE name=VAR COLON ty=lambdaterm {(name, ty)} 

/* PARTIE 5 : TERMS ************************************** */                                                         

lambdaterm:
  | FUN bs=fun_binders BIGARROW e=lambdaterm {
      List.fold_right (fun (x, t) acc -> Func(x, t, acc)) bs e
    }
  | pi_term { $1 }

fun_binders:
  | b=fun_binder { [b] }
  | b=fun_binder bs=fun_binders { b :: bs }

fun_binder:
  | LPAREN x=VAR COLON t=lambdaterm RPAREN { (x, t) }

pi_term:
  | FORALL x=VAR COLON a=lambdaterm COMMA b=pi_term { Pi(x, a, b) }
  | a=applic SMALLARROW b=pi_term { Pi("_", a, b) }
  | applic { $1 }

applic:
  | f=applic a=atom { App(f, a) }
  | atom { $1 }

atom:
  | TYPE { Type }
  | t=VAR { Var t }
  | GOAL LPAREN t=lambdaterm RPAREN { Goal(0, t) }
  | LPAREN t=lambdaterm RPAREN { t }

/* PARTIE 6 : TACTICS ************************************** */                                                         

tactic_dot:
  | tactic DOT { $1 }

tactic:
  | INTRO x=VAR { Intro(x) }
  | TRIVIAL { Trivial }
  | APPLY x=VAR { Apply(x) }
  | EXACT t=lambdaterm { Exact(t) }
