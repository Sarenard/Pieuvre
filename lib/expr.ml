type lambdaterm =
  (*Variables*)
  | Var of string
  
  (*universes ?*)
  | Type

  (**)
  | Goal of int * lambdaterm
  
  (*functions*)
  | Pi of string * lambdaterm * lambdaterm
  | Func of string * lambdaterm * lambdaterm (* nom arg, type arg, contenu*)
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
  | Qed
  | Exact of lambdaterm
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

let rec free_and_bound term bound = match term with
  | Var s -> if List.mem s bound then ([], bound) else ([s], bound)
  | Func(s, ty, body) -> free_and_bound body (s::bound)
  | App(t1, t2) ->
    let (f1, b1) = free_and_bound t1 bound in
    let (f2, b2) = free_and_bound t2 bound in
    (f1 @ f2, b1 @ b2)
  | _ -> ([], [])

let get_fresh v lst =
  let len = String.length v in
  (* Find the index where digits start *)
  let rec find_digit_start i =
    if i >= len then len
    else
      match v.[i] with
      | '0' .. '9' -> i
      | _ -> find_digit_start (i + 1)
  in
  let i = find_digit_start 0 in
  let prefix = String.sub v 0 i in
  let number =
    if i = len then 0
    else int_of_string (String.sub v i (len - i))
  in
  let rec find n =
    let candidate = prefix ^ string_of_int n in
    if List.mem candidate lst then find (n + 1)
    else candidate
  in find number

let rec replace term x x' = match term with
  | Var s -> if s = x then x' else Var s
  | Func(s, ty, body) -> 
    if s = x then term
    else (
      let x'free, _ = free_and_bound x' [] in
      if List.mem s x'free then ( 
        let bfree, bbound = free_and_bound body [] in
        let spoiled = x'free @ bfree @ bbound in
        let fresh = get_fresh s spoiled in
        Func(fresh, ty, replace (replace body s (Var fresh)) x x')
      ) else Func(s, ty, replace body x x')
    )
  | Pi(s, ty, body) -> 
    if s = x then term
    else (
      let x'free, _ = free_and_bound x' [] in
      if List.mem s x'free then ( 
        let bfree, bbound = free_and_bound body [] in
        let spoiled = x'free @ bfree @ bbound in
        let fresh = get_fresh s spoiled in
        Pi(fresh, ty, replace (replace body s (Var fresh)) x x')
      ) else Pi(s, ty, replace body x x')
    )
  | App(t1, t2) -> App(replace t1 x x', replace t2 x x')
  | Type -> Type
  | Goal(i, tm) -> Goal(i, replace tm x x')

let rec betastep term : lambdaterm option =
  match term with
  | Var _ -> None
  | Type -> None
  | Goal(_, _) -> None
  | Pi(_, _, _) -> None
  | Func(v, ty, body) -> (match (betastep body) with
    | Some t -> Some (Func(v, ty, t)) 
    | None -> None
    )
  | App(Func(v, ty, body), t) -> Some (replace body v t)
  | App(f, t) -> (match (betastep f) with
    | Some f' -> Some (App(f', t))
    | None -> (match betastep t with
      | Some t' -> Some (App(f, t'))
      | None -> None
    )
  )
;;

let rec reduce term : lambdaterm =
  let newterm = betastep term in
  match newterm with
    | Some(inside) -> reduce inside
    | None -> term
;;

exception Type_error;;
exception Unbound_variable of string;;

let rec infer (gamma:context) (term:lambdaterm) : lambdaterm =
  match term with
  | Var(x) -> (
    try List.assoc x gamma
    with Not_found -> raise (Unbound_variable x) 
  )
  | Type -> Type
  | Goal(_, a) -> a
  (*TODO : more checks here ?*)
  | Pi(_, _, _) -> Type 
  (*TODO : more checks here ? (ty is Type ?)*)
  | Func(v, ty, body) -> 
    Pi(v, ty, infer ((v, ty)::gamma) body)
  | App(f, t) -> (
    match reduce (infer gamma f) with
    | Pi(x, a, b) -> 
      typecheck gamma t a;
      reduce (replace b x t)
    | _ -> raise Type_error
  )

and typecheck (gamma:context) (term:lambdaterm) (ty:lambdaterm) : unit =
  let type_of_term = infer gamma term in
  if (alpha (reduce type_of_term) (reduce ty)) then
    ()
  else
    raise Type_error
;;
