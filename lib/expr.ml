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
  | Exact of lambdaterm
  | Apply of string
  (*| Exact of lambdaterm*)
[@@deriving show]
;;

type constructor =
  (*<name> : <pos_type>*)
  | Constructor of string * lambdaterm
[@@deriving show]
;;

type statement =
  (*th <name> : Goal(...)*)
  | Theorem of string * lambdaterm
  | Proof of tactic list
  (*
  Inductive <name> : <arity> :=
  <[
    constructor
  ]>
  *)
  | Inductive of string * lambdaterm * constructor list
[@@deriving show]
;;

let rec affiche_lam = function
  | Var(x) -> print_string x
  | Type -> print_string "Type"
  (*TODO : show only when nessessary*)
  | Pi(x, a, b) ->
    if x = "_" then
      (
        print_string "(";
        affiche_lam a;
        print_string " -> ";
        affiche_lam b;
        print_string ")";
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
  | Func(s, ty, body) -> 
    let (f1, b1) = free_and_bound ty bound in
    let (f2, b2) = free_and_bound body (s::bound) in
    (f1 @ f2, b1 @ b2)
  | Pi(s, ty, body) -> 
    let (f1, b1) = free_and_bound ty bound in
    let (f2, b2) = free_and_bound body (s::bound) in
    (f1 @ f2, b1 @ b2)
  | App(t1, t2) ->
    let (f1, b1) = free_and_bound t1 bound in
    let (f2, b2) = free_and_bound t2 bound in
    (f1 @ f2, b1 @ b2)
  | Type -> ([], bound)
  | Goal(_, goal) -> free_and_bound goal bound
;;

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
    if s = x then Func(s, replace ty x x', body)
    else (
      let x'free, _ = free_and_bound x' [] in
      if List.mem s x'free then ( 
        let bfree, bbound = free_and_bound body [] in
        let bfree', bbound' = free_and_bound ty [] in
        let spoiled = x'free @ bfree @ bbound @ bfree' @ bbound' in
        let fresh = get_fresh s spoiled in
        Func(fresh, replace (replace ty s (Var fresh)) x x', replace (replace body s (Var fresh)) x x')
      ) else Func(s, replace ty x x', replace body x x')
    )
  | Pi(s, ty, body) -> 
    if s = x then Pi(s, replace ty x x', body)
    else (
      let x'free, _ = free_and_bound x' [] in
      if List.mem s x'free then ( 
        let bfree, bbound = free_and_bound body [] in
        let bfree', bbound' = free_and_bound ty [] in
        let spoiled = x'free @ bfree @ bbound @ bfree' @ bbound' in
        let fresh = get_fresh s spoiled in
        Pi(fresh, replace (replace ty s (Var fresh)) x x', replace (replace body s (Var fresh)) x x')
      ) else Pi(s, replace ty x x', replace body x x')
    )
  | App(t1, t2) -> App(replace t1 x x', replace t2 x x')
  | Type -> Type
  | Goal(i, tm) -> Goal(i, replace tm x x')

let rec betastep term : lambdaterm option =
  match term with
  | Var _ -> None
  | Type -> None
  | Goal(i, t) ->
    (match betastep t with
    | Some t' -> Some (Goal(i, t'))
    | None -> None)
  | Pi(x, a, b) ->
    (match betastep a with
    | Some a' -> Some (Pi(x, a', b))
    | None ->
      match betastep b with
      | Some b' -> Some (Pi(x, a, b'))
      | None -> None)
  | Func(v, ty, body) ->
    (match betastep ty with
    | Some ty' -> Some (Func(v, ty', body))
    | None ->
      match betastep body with
      | Some body' -> Some (Func(v, ty, body'))
      | None -> None)
  | App(Func(v, _ty, body), t) ->
      Some (replace body v t)
  | App(f, t) ->
    (match betastep f with
    | Some f' -> Some (App(f', t))
    | None ->
      match betastep t with
      | Some t' -> Some (App(f, t'))
      | None -> None)
;;


let rec reduce term : lambdaterm =
  let newterm = betastep term in
  match newterm with
    | Some(inside) -> reduce inside
    | None -> term
;;

let equiv a b = 
  alpha (reduce a) (reduce b)
;;

let empty_env = [

];;

exception Type_error;;
exception Unexpected_goal;;
exception Unbound_variable of string;;

(*we will need to change that with universes*)
let rec check_is_type gamma ty =
  match reduce (infer gamma ty) with
  | Type -> ()
  | _ -> raise Type_error

and infer (gamma:context) (term:lambdaterm) : lambdaterm =
  match term with
  | Var(x) -> (
    try List.assoc x gamma
    with Not_found -> raise (Unbound_variable x) 
  )
  (*This will cause problems but for now it is totally fine : we ignore universes*)
  | Type -> Type
  | Goal(_, _a) -> raise Unexpected_goal;
  | Pi(x, a, b) -> 
    check_is_type gamma a;
    check_is_type ((x, a)::gamma) b;
    Type 
  | Func(v, ty, body) -> 
    check_is_type gamma ty;
    let new_context = ((v, ty)::gamma) in
    let body_type = infer new_context body in
    check_is_type new_context body_type;
    Pi(v, ty, body_type)
  | App(f, t) -> (
    match reduce (infer gamma f) with
    | Pi(x, a, b) -> 
      typecheck gamma t a;
      reduce (replace b x t)
    | _ -> raise Type_error
  )

and typecheck (gamma:context) (term:lambdaterm) (ty:lambdaterm) : unit =
  let type_of_term = infer gamma term in
  if equiv type_of_term ty then
    ()
  else
    raise Type_error
;;
