type lambdaterm =
  (*Variables*)
  | Var of string
  
  (*We will later need to handle Prop and Type(i)*)
  | Type

  (**)
  | Goal of int * lambdaterm
  
  (*functions*)
  | Pi of string * lambdaterm * lambdaterm
  (* nom arg, type arg, contenu*)
  | Func of string * lambdaterm * lambdaterm 
  | App of lambdaterm * lambdaterm

  (*Inductive*)
  (*indice dans la liste des inductifs*)
  | Inductive of int
  (*indice dans la liste des inductifs, id_constru, (liste des args du constructeur)*)
  | Constructor of int * int * lambdaterm list

[@@deriving show]
;;

let rec affiche_lam_list = function
  | [] -> ""
  | [t] -> affiche_lam t
  | t :: q ->
    affiche_lam t ^ "; " ^ affiche_lam_list q

and affiche_lam ty : string = 
  let prec = function
    | Var _ | Type | Inductive(_) | Constructor(_, _, _) | Goal(_) -> 10
    | App(_, _) -> 5
    | Pi(_, _, _) -> 3
    | Func(_, _, _) -> 1
  in
  let pself = prec ty in
  let paren e : string = 
    if prec e <= pself then "(" ^ affiche_lam e ^ ")" else affiche_lam e
  in
  let sparen e : string = 
    if prec e < pself then "(" ^ affiche_lam e ^ ")" else affiche_lam e
  in
  match ty with
  | Var(x) -> x
  | Type -> "Type"
  | Inductive nb ->
    "<Inductive(" ^ string_of_int nb ^ ")>";
  | Constructor(a, b, lt) ->
    "<Constructor(" ^ string_of_int a ^ ", " ^ string_of_int b ^ ", [" ^ affiche_lam_list lt ^ "])>";
  | Pi("_", a, b) ->
    paren a ^ " -> " ^ sparen b
  | Pi(x, a, b) -> "(" ^ x ^ " : " ^ affiche_lam a ^ ") -> " ^ sparen b
  | Func(x, a, b) -> "fun " ^ x ^ " : " ^ affiche_lam a ^ " => " ^ affiche_lam b
  | App(a, b) -> sparen a ^ " " ^ paren b
  | Goal(_, a) -> "Goal(" ^ affiche_lam a ^ ")"
;;

let pp_lambdaterm fmt t =
  Format.pp_print_string fmt (affiche_lam t)

let show_lambdaterm t =
  Format.asprintf "%a" pp_lambdaterm t

type tactic = 
| Intro of string
| Trivial
| Exact of lambdaterm
| Apply of string
(*| Exact of lambdaterm*)
[@@deriving show]
;;

type constructor = (string * lambdaterm)
[@@deriving show]
;;


type inductive_type = (string * lambdaterm * constructor list)
[@@deriving show]
;;

type context = {
  gamma : (string * lambdaterm) list;
  values : (string * lambdaterm) list;
  inductive_types : inductive_type list;
}
[@@deriving show]
;;

type statement =
  (*th <name> : Goal(...)*)
  | STheorem of string * lambdaterm
  | SProof of tactic list
  (*
  Inductive <name> : <arity> :=
  <[
    constructor
  ]>
  *)
  | SInductive of inductive_type
[@@deriving show]
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
    | Inductive i1, Inductive i2 -> i1 = i2
    | Constructor (c1, i1, args1), Constructor (c2, i2, args2) ->
        c1 = c2
        && i1 = i2
        && List.length args1 = List.length args2
        && List.for_all2 (alpha_aux env12 env21) args1 args2
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
  | Goal(_, goal) -> free_and_bound goal bound
  | Type -> ([], bound)
  | Inductive(_) -> ([], bound) 
  | Constructor(_, _, args) ->
    List.fold_left
      (fun (free_acc, bound_acc) arg ->
        let (free_arg, bound_arg) = free_and_bound arg bound_acc in
        (free_acc @ free_arg, bound_acc @ bound_arg))
      ([], bound)
      args
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
  | Inductive(i) -> Inductive(i)
  | Constructor(i, j, args) ->
    Constructor(i, j, List.map (fun arg -> replace arg x x') args)

let rec betastep (ctx:context) (term:lambdaterm) : lambdaterm option =
  match term with
  | Var _ -> None
  | Type -> None
  | Inductive(i) -> None
  | Constructor(i, j, args) ->
    let rec aux acc = function
      | [] -> None
      | t :: q ->
          match betastep ctx t with
          | Some t' -> Some (Constructor(i, j, List.rev_append acc (t' :: q)))
          | None -> aux (t :: acc) q
    in
    aux [] args
  | Goal(i, t) ->
    (match betastep ctx t with
    | Some t' -> Some (Goal(i, t'))
    | None -> None)
  | Pi(x, a, b) ->
    (match betastep ctx a with
    | Some a' -> Some (Pi(x, a', b))
    | None ->
      match betastep ctx b with
      | Some b' -> Some (Pi(x, a, b'))
      | None -> None)
  | Func(v, ty, body) ->
    (match betastep ctx ty with
    | Some ty' -> Some (Func(v, ty', body))
    | None ->
      match betastep ctx body with
      | Some body' -> Some (Func(v, ty, body'))
      | None -> None)
  | App(Func(v, _ty, body), t) ->
    Some (replace body v t)
  | App(Constructor(i, j, lst), t) ->
    Some(Constructor(i, j, lst @ [t]))
  | App(Var(x), t) -> (
    match List.assoc_opt x ctx.gamma with
    | Some (Constructor (i, j, lst)) -> Some (Constructor (i, j, lst @ [t]))
    | Some (Inductive(i)) -> Some (App(Inductive(i), t))
    | _ ->
      match betastep ctx t with
      | Some t' -> Some (App(Var(x), t'))
      | None -> None
    )
  | App(f, t) ->
    (match betastep ctx f with
    | Some f' -> Some (App(f', t))
    | None ->
      match betastep ctx t with
      | Some t' -> Some (App(f, t'))
      | None -> None)
;;

let rec reduce (ctx:context) term : lambdaterm =
  let newterm = betastep ctx term in
  match newterm with
    | Some(inside) -> reduce ctx inside
    | None -> term
;;

let equiv (ctx:context) a b = 
  alpha (reduce ctx a) (reduce ctx b)
;;

let empty_env = { gamma = []; inductive_types = []; values = []};;

exception Type_error;;
exception Unexpected_goal;;
exception Unbound_variable of string;;

(*we will need to change that with universes*)
let rec check_is_type gamma ty =
  match reduce gamma (infer gamma ty) with
  | Type -> ()
  | _ -> raise Type_error

and infer (gamma:context) (term:lambdaterm) : lambdaterm =
  let gamma_var = gamma.gamma in
  let gamma_ind = gamma.inductive_types in
  let gamma_val = gamma.values in
  match reduce gamma term with
  | Var(x) -> (
    try List.assoc x gamma_var
    with Not_found -> raise (Unbound_variable x) 
  )
  (*This will cause problems but for now it is totally fine : we ignore universes*)
  | Type -> Type
  | Goal(_, _a) -> raise Unexpected_goal;
  | Pi(x, a, b) -> 
    let new_context = { gamma = (x, a) :: gamma_var; inductive_types = gamma_ind; values = gamma_val } in
    check_is_type gamma a;
    check_is_type new_context b;
    Type 
  | Func(v, ty, body) -> 
    check_is_type gamma ty;
    let new_context = { gamma = (v, ty) :: gamma_var; inductive_types = gamma_ind; values = gamma_val } in
    let body_type = infer new_context body in
    check_is_type new_context body_type;
    Pi(v, ty, body_type)
  | App(f, t) -> (
    match infer gamma (reduce gamma f) with
    | Pi(x, a, b) -> 
      typecheck gamma t a;
      reduce gamma (replace b x t)
    | _ -> 
      print_endline "Erreur de type dans un app";
      raise Type_error;
  )
  | Inductive(_) ->
    assert false;
  | Constructor(_) ->
    assert false;

and typecheck (gamma:context) (term:lambdaterm) (ty:lambdaterm) : unit =
  let type_of_term = infer gamma term in
  if equiv gamma type_of_term ty then
    ()
  else
    raise Type_error
;;

let rec occurs_bound bound name term =
  match term with
  | Var x -> x = name && not (List.mem x bound)
  | Type -> false
  | Inductive(i) -> false
  | Constructor(i, j, args) -> List.exists (occurs_bound bound name) args
  | Goal (_, a) -> occurs_bound bound name a
  | Pi (x, a, b) ->
    occurs_bound bound name a || occurs_bound (x :: bound) name b
  | Func (x, a, b) ->
    occurs_bound bound name a || occurs_bound (x :: bound) name b
  | App (a, b) ->
    occurs_bound bound name a || occurs_bound bound name b
;;

(*https://link.springer.com/content/pdf/10.1007/BFb0037116.pdf*)
let check_wellformed_inductive (name:string) (gamma:context) (arity:lambdaterm) (constructors:constructor list) : unit =
  let gamma_var = gamma.gamma in
  let gamma_ind = gamma.inductive_types in
  let gamma_val = gamma.values in

  (*Step 1 : Check the arity*)
  let rec check_arity gamma' ty = match ty with
    | Type -> ()
    | Pi(x, a, b) ->
      let bigger_context = (x, a) :: gamma' in 
      check_is_type { gamma = gamma'; inductive_types = gamma_ind; values = gamma_val } a;
      check_arity bigger_context b 
    | _ -> failwith "Arity of an inductive type is malformed"
  in check_arity gamma_var arity;

  (*Step 2 : Check the constructors*)
  let check_one = function (_ctor_name, ty) ->
    (*
    TODO : check positivity when under other types
    Example of a problematic case :
    Inductive bad
    | mk : (option bad -> A) -> bad
    And an ok case :
    Inductive nat
    | c : option nat -> nat
    For this we will need to save the polarity of every argument of every inductive type.
    *)
    let rec is_strict_positive bound ty : bool =
      match ty with
      | Var x -> x = name && not (List.mem x bound)
      | App(a, b) when is_strict_positive bound a && not (occurs_bound bound name b) -> true
      | Pi(x, a, b) when is_strict_positive (x :: bound) b && not (occurs_bound bound name a) -> true
      | _ -> false
    in let rec is_constructor bound ty : bool =
      match ty with
      | Var x -> x = name && not (List.mem x bound)
      | Pi("_", a, b) when is_constructor bound b && is_strict_positive bound a -> true
      | Pi(x, a, b) when is_constructor (x :: bound) b && not (occurs_bound bound name a) -> true
      | App(a, b) when is_constructor bound a && not (occurs_bound bound name b) -> true
      | _ -> false
    in 
    let new_env = { gamma = (name, arity) :: gamma_var; inductive_types = gamma_ind ; values = gamma_val} in
    check_is_type new_env ty;
    if not (is_constructor [] ty) then failwith ("Malformed constructor in " ^ name)
  in
  List.iter check_one constructors;
;;
