type lambdaterm =
  (*Variables*)
  | Var of string
  
  (*universes ?*)
  | Type

  (**)
  | Goal of int * lambdaterm
  
  (*functions*)
  | Pi of string * lambdaterm * lambdaterm
  | Func of string * lambdaterm * lambdaterm
  | App of lambdaterm * lambdaterm
[@@deriving show]
;;

type context = 
  (string * lambdaterm) list
[@@deriving show]
;;

type tactic = 
  | Intro of string
  | Trivial
  (*| Exact of lambdaterm*)
[@@deriving show]
;;

let rec affiche_lam = function
  | Var(x) -> print_string x
  | Type -> print_string "Type"
  | Pi(x, a, b) ->
    if x = "_" then
      (
        affiche_lam a;
        print_string " -> ";
        affiche_lam b;
      )
    else
      (
        print_string "Pi(";
        print_string x;
        print_string ", ";
        affiche_lam a;
        print_string ", ";
        affiche_lam b;
        print_string ")";
      )
  | Func(x, a, b) ->
    print_string "fun (";
    print_string x;
    print_string ":";
    affiche_lam a;
    print_string ") => ";
    affiche_lam b;
  | App(a, b) ->
    print_string "(";
    affiche_lam a;
    print_string ") (";
    affiche_lam b;
    print_string ")";
  | Goal(i, a) ->
    print_string "Goal(";
    print_int i;
    print_string ", ";
    affiche_lam a;
    print_string ")";
;;

let numerote (term:lambdaterm) : lambdaterm =
  let next = ref 1 in
  let rec dfs term =
    match term with
    | Var _ | Type -> term
    | Goal (_, a) ->
        let i = !next in
        incr next;
        Goal (i, a)
    | Pi (x, a, b) -> Pi (x, a, b)
    | Func (x, a, b) -> Func (x, a, dfs b)
    | App (a, b) -> App (dfs a, dfs b)
  in
  dfs term
;;

let alpha term1 term2 =
  let rec alpha_aux env12 env21 term1 term2 =
    match (term1, term2) with
    | Var x, Var y -> (
        match (List.assoc_opt x env12, List.assoc_opt y env21) with
        | Some y', Some x' -> String.equal y y' && String.equal x x'
        | None, None -> String.equal x y
        | _ -> false
      )
    | Type, Type -> true
    | Goal(_, t1), Goal(_, t2) -> alpha_aux env12 env21 t1 t2
    | Pi (x, a1, b1), Pi (y, a2, b2)
    | Func (x, a1, b1), Func (y, a2, b2) ->
        alpha_aux env12 env21 a1 a2
        && alpha_aux ((x, y) :: env12) ((y, x) :: env21) b1 b2
    | App (f1, x1), App (f2, x2) ->
        alpha_aux env12 env21 f1 f2
        && alpha_aux env12 env21 x1 x2
    | _ -> false
  in
  alpha_aux [] [] term1 term2
;;

let betastep term : lambdaterm option =
  None
;;

let rec reduce term : lambdaterm =
  let newterm = betastep term in
  match newterm with
    | Some(inside) -> reduce inside
    | None -> term
;;

(*typecheck : gam -> lam -> ty -> bool*)
