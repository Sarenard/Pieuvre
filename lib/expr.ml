type mvar = int
[@@deriving show]
;;

(*TODO : separate the kernel and the userlevel lambdaterms so that the kernel can be pure*)
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
  | Recursor of int * lambdaterm list
  (*indice dans la liste des inductifs, id_constru, (liste des args du constructeur)*)
  | Constructor of int * int * lambdaterm list

  (*Unification*)
  | Mvar of mvar (*?x*)

  (* produits *)
  | Prod of lambdaterm * lambdaterm (* le type *)
  | Pair of lambdaterm * lambdaterm
  | Fst of lambdaterm
  | Snd of lambdaterm

  (* sums *)
  | Sum of lambdaterm * lambdaterm (* le type *)
  | InL of lambdaterm * lambdaterm (* element, type of B *)
  | InR of lambdaterm * lambdaterm (* type of A, element *)
  | Match of lambdaterm * lambdaterm * lambdaterm (* types A \/ B, A -> C, B -> C *)

[@@deriving show]
;;

type tactic = 
| Intro of string
| Trivial
| Exact of lambdaterm
| Apply of string
(*| Exact of lambdaterm*)
| Cut of lambdaterm
| Split
| Destruct of string
| Left
| Right
| Simpl
[@@deriving show]
;;

type constructor = (string * lambdaterm)
[@@deriving show]
;;

type inductive_type = (string * lambdaterm * constructor list)
[@@deriving show]
;;

(*TODO : separate gamma into local env and global env*)
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
  | SDefinition of string * lambdaterm * lambdaterm
[@@deriving show]
;;

let affiche_lam_with_inductives inductive_types ty : string =
  let rec aux ty =
    let prec = function
      | Var _ | Type | Inductive(_) | Recursor(_, _) | Constructor(_, _, _) | Goal(_) | Mvar _ -> 10
      | App(_, _) -> 5
      | Pi(_, _, _) -> 3
      | Func(_, _, _) -> 1
      | _ -> 0
    in
    let pself = prec ty in
    let paren e : string =
      if prec e <= pself then "(" ^ aux e ^ ")" else aux e
    in
    let sparen e : string =
      if prec e < pself then "(" ^ aux e ^ ")" else aux e
    in
    let show_inductive nb =
      match List.nth_opt inductive_types nb with
      | Some (name, _, _) -> name
      | None -> "<Inductive(" ^ string_of_int nb ^ ")>"
    in
    let show_recursor ind_idx args =
      match List.nth_opt inductive_types ind_idx with
      | Some (name, _, _) ->
          List.fold_left (fun acc arg -> acc ^ " " ^ paren arg) (name ^ "_rec") args
      | None ->
          "<Recursor(" ^ string_of_int ind_idx ^ ", ["
          ^ String.concat "; " (List.map aux args) ^ "])>"
    in
    let show_constructor ind_idx cst_idx args =
      match List.nth_opt inductive_types ind_idx with
      | Some (_, _, constructors) -> (
          match List.nth_opt constructors cst_idx with
          | Some (name, _) ->
              List.fold_left (fun acc arg -> acc ^ " " ^ paren arg) name args
          | None ->
              "<Constructor(" ^ string_of_int ind_idx ^ ", " ^ string_of_int cst_idx
              ^ ", [" ^ String.concat "; " (List.map aux args) ^ "])>"
        )
      | None ->
          "<Constructor(" ^ string_of_int ind_idx ^ ", " ^ string_of_int cst_idx
          ^ ", [" ^ String.concat "; " (List.map aux args) ^ "])>"
    in
    match ty with
    | Var(x) -> x
    | Mvar(i) -> "(?" ^ string_of_int i ^ ")"
    | Type -> "Type"
    | Inductive nb -> show_inductive nb
    | Recursor(ind_idx, args) -> show_recursor ind_idx args
    | Constructor(a, b, lt) -> show_constructor a b lt
    | Pi("_", a, b) ->
      paren a ^ " -> " ^ sparen b
    | Pi(x, a, b) -> "(" ^ x ^ " : " ^ aux a ^ ") -> " ^ sparen b
    | Func(x, a, b) -> "fun " ^ x ^ " : " ^ aux a ^ " => " ^ aux b
    | App(a, b) -> sparen a ^ " " ^ paren b
    | Goal(_, a) -> "Goal(" ^ aux a ^ ")"
    | Prod(a, b) -> paren a ^ " /\\ " ^ paren b
    | Pair(a, b) -> "(" ^ aux a ^ ", " ^ aux b ^ ")"
    | Fst(a) -> "Fst(" ^ aux a ^ ")"
    | Snd(a) -> "Snd(" ^ aux a ^ ")"
    | InL(a, b) -> "InL(" ^ aux a ^ ", " ^ aux b ^ ")"
    | InR(a, b) -> "InR(" ^ aux a ^ ", " ^ aux b ^ ")"
    | Sum(a, b) -> paren a ^ " \\/ " ^ paren b
    | Match(a, b, c) -> "match " ^ aux a ^ " with " ^ aux b ^ " || " ^ aux c
  in
  aux ty
;;

let affiche_lam ty : string =
  affiche_lam_with_inductives [] ty
;;

let affiche_lam_in_ctx (ctx : context) ty : string =
  affiche_lam_with_inductives ctx.inductive_types ty
;;

(*
We shadow the functions defined by the ppx show
*)
let pp_lambdaterm fmt t =
  Format.pp_print_string fmt (affiche_lam t)

let pp_lambdaterm_in_ctx ctx fmt t =
  Format.pp_print_string fmt (affiche_lam_in_ctx ctx t)

let show_lambdaterm t =
  Format.asprintf "%a" pp_lambdaterm t

let show_lambdaterm_in_ctx ctx t =
  Format.asprintf "%a" (pp_lambdaterm_in_ctx ctx) t

(*
Checks alpha-equivalence
*)
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
    | Goal(_, t1), Goal(_, t2)
    | Fst(t1), Fst(t2)
    | Snd(t1), Snd(t2) -> alpha_aux env12 env21 t1 t2
    | Pi (x, a1, b1), Pi (y, a2, b2)
    | Func (x, a1, b1), Func (y, a2, b2) ->
        alpha_aux env12 env21 a1 a2
        && alpha_aux ((x, y) :: env12) ((y, x) :: env21) b1 b2
    | App (f1, x1), App (f2, x2)
    | Pair(f1, x1), Pair(f2, x2)
    | Prod(f1, x1), Prod(f2, x2)
    | Sum(f1, x1), Sum(f2, x2)
    | InL(f1, x1), InL(f2, x2)
    | InR(f1, x1), InR(f2, x2) ->
        alpha_aux env12 env21 f1 f2
        && alpha_aux env12 env21 x1 x2
    | Inductive i1, Inductive i2 -> i1 = i2
    | Recursor (i1, args1), Recursor (i2, args2) ->
        i1 = i2
        && List.length args1 = List.length args2
        && List.for_all2 (alpha_aux env12 env21) args1 args2
    | Constructor (c1, i1, args1), Constructor (c2, i2, args2) ->
        c1 = c2
        && i1 = i2
        && List.length args1 = List.length args2
        && List.for_all2 (alpha_aux env12 env21) args1 args2
    | Match(a, b, c), Match(a', b', c') ->
      alpha_aux env12 env21 a a' && alpha_aux env12 env12 b b' && alpha_aux env12 env21 c c'
    | _ -> false
  in
  alpha_aux [] [] term1 term2
;;

(*
gets all of the bound variables of a term
*)
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
  | App(t1, t2) | Pair(t1, t2) | Prod(t1, t2) | Sum(t1, t2) | InL(t1, t2) | InR(t1, t2) ->
    let (f1, b1) = free_and_bound t1 bound in
    let (f2, b2) = free_and_bound t2 bound in
    (f1 @ f2, b1 @ b2)
  | Goal(_, goal) -> free_and_bound goal bound
  | Type -> ([], bound)
  | Mvar(_) -> ([], bound)
  | Inductive(_) -> ([], bound) 
  | Recursor(_, args)
  | Constructor(_, _, args) ->
    List.fold_left
      (fun (free_acc, bound_acc) arg ->
        let (free_arg, bound_arg) = free_and_bound arg bound in
        (free_acc @ free_arg, bound_acc @ bound_arg))
      ([], bound)
      args
  | Fst(x) | Snd(x) -> free_and_bound x bound
  | Match(a, b, c) -> 
    let (f1, b1) = free_and_bound a bound in
    let (f2, b2) = free_and_bound b bound in
    let (f3, b3) = free_and_bound c bound in
    (f1 @ f2 @ f3, b1 @ b2 @ b3)
;;

(*
Gets every unfresh variable of a term
*)
let unfresh term =
  let free, bound = free_and_bound term [] in free@bound
;;

(*
Generates a fresh variable (trying to match the name v)
x0 -> xi with i the smallest so that it is not taken
*)
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

(*
replaces x with x' in term
*)
let rec replace term x x' = match term with
  | Var s -> if s = x then x' else Var s
  | Mvar _ -> term
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
  | Type -> term
  | Goal(i, tm) -> Goal(i, replace tm x x')
  | Inductive(i) -> term
  | Recursor(i, args) ->
    Recursor(i, List.map (fun arg -> replace arg x x') args)
  | Constructor(i, j, args) ->
    Constructor(i, j, List.map (fun arg -> replace arg x x') args)
  | Fst(t) -> Fst(replace t x x')
  | Snd(t) -> Snd(replace t x x')
  | Pair(t, t') -> Pair(replace t x x', replace t' x x')
  | Prod(t, t') -> Prod(replace t x x', replace t' x x')
  | Sum(t, t') -> Sum(replace t x x', replace t' x x')
  | InL(t, t') -> InL(replace t x x', replace t' x x')
  | InR(t, t') -> InR(replace t x x', replace t' x x')
  | Match(t, t', t'') -> Match(replace t x x', replace t' x x', replace t'' x x')


(*
Does one step of a beta-reduction
Do we want to go with a big steps approach?
*)
let rec betastep (ctx:context) (term:lambdaterm) : lambdaterm option =
  let rec count_pis = function
    | Pi(_, _, body) -> 1 + count_pis body
    | _ -> 0
  in
  let recursor_arity i =
    let (ind_name, _arity, _constructors) = List.nth ctx.inductive_types i in
    let recursor_ty =
      try List.assoc (ind_name ^ "_rec") ctx.gamma
      with Not_found -> failwith ("Missing recursor type for " ^ ind_name)
    in
    count_pis recursor_ty
  in
  match term with
  | Var(x) -> List.assoc_opt x ctx.values
  | Mvar _ -> None
  | Type -> None
  | Inductive(i) -> None
  | Recursor(i, args) ->
    if List.length args >= recursor_arity i then
      failwith "Computation of recursors here"
    else
      let rec aux acc = function
        | [] -> None
        | t :: q ->
            match betastep ctx t with
            | Some t' -> Some (Recursor(i, List.rev_append acc (t' :: q)))
            | None -> aux (t :: acc) q
      in
      aux [] args
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
  | App(Recursor(i, lst), t) ->
    if List.length lst < recursor_arity i then
      Some(Recursor(i, lst @ [t]))
    else
      (match betastep ctx (Recursor(i, lst)) with
      | Some rec' -> Some(App(rec', t))
      | None ->
        match betastep ctx t with
        | Some t' -> Some(App(Recursor(i, lst), t'))
        | None -> None)
  | App(Constructor(i, j, lst), t) ->
    Some(Constructor(i, j, lst @ [t]))
  | App(Var(x), t) -> (
    match List.assoc_opt x ctx.values with
    | Some (Constructor (i, j, lst)) -> Some (Constructor (i, j, lst @ [t]))
    | Some (Inductive(i)) -> Some (App(Inductive(i), t))
    | Some (Recursor(i, lst)) ->
      if List.length lst < recursor_arity i then
        Some (Recursor(i, lst @ [t]))
      else
        Some (App(Recursor(i, lst), t))
    | Some v -> Some (App(v, t))
    | None ->
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
  | Fst(t) -> (match betastep ctx t with
    | Some t' -> Some (Fst(t'))
    | None -> (match t with
      | Pair(a, _) -> Some a
      | _ -> None
    )
  )
  | Snd(t) -> (match betastep ctx t with
    | Some t' -> Some (Snd(t'))
    | None -> (match t with
      | Pair(_, b) -> Some b
      | _ -> None
    )
  )
  | Prod(f, t) ->
    (match betastep ctx f with
    | Some f' -> Some (Prod(f', t))
    | None ->
      match betastep ctx t with
      | Some t' -> Some (Prod(f, t'))
      | None -> None)
  | Pair(f, t) ->
    (match betastep ctx f with
    | Some f' -> Some (Pair(f', t))
    | None ->
      match betastep ctx t with
      | Some t' -> Some (Pair(f, t'))
      | None -> None)
  | Sum(f, t) ->
    (match betastep ctx f with
    | Some f' -> Some (Sum(f', t))
    | None ->
      match betastep ctx t with
      | Some t' -> Some (Sum(f, t'))
      | None -> None)
  | InL(f, t) ->
    (match betastep ctx f with
    | Some f' -> Some (InL(f', t))
    | None ->
      match betastep ctx t with
      | Some t' -> Some (InL(f, t'))
      | None -> None)
  | InR(f, t) ->
    (match betastep ctx f with
    | Some f' -> Some (InR(f', t))
    | None ->
      match betastep ctx t with
      | Some t' -> Some (InR(f, t'))
      | None -> None)
  | Match(InL(a, _), t, _) -> Some(App(t, a))
  | Match(InR(_, b), _, t) -> Some(App(t, b))
  | Match(f, t, t2) ->
    (match betastep ctx f with
    | Some f' -> Some (Match(f', t, t2))
    | None ->
      match betastep ctx t with
      | Some t' -> Some (Match(f, t', t2))
      | None -> (match betastep ctx t2 with
        | Some t'' -> Some (Match(f, t, t''))
        | None -> None
      ))
;;

(*
Full beta reduction
*)
let rec reduce (ctx:context) term : lambdaterm =
  let newterm = betastep ctx term in
  match newterm with
    | Some(inside) -> reduce ctx inside
    | None -> term
;;

(*
Alpha-beta equivalence
*)
let equiv (ctx:context) a b = 
  alpha (reduce ctx a) (reduce ctx b)
;;

(*
We keep that becaue it is easier to give an empty env
and so that we have it if one day we need to have things in the empty_env
*)
let empty_env () = { gamma = []; inductive_types = []; values = []};;

exception Type_error;;
exception Unexpected_goal;;
exception Unbound_variable of string;;

let debug s = (*print_endline s*) ()

(*
This checks if something is of type Type
  we will need to change that when we will handle universes
*)
let rec check_is_type gamma ty =
  match reduce gamma (infer gamma ty) with
  | Type -> ()
  | _ -> raise Type_error

(*
this takes a term and returns its type
*)
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
  | Mvar _ -> failwith "We dont want a Mvar here";
  | Goal(_, _a) -> raise Unexpected_goal;
  | Pi(x, a, b) -> 
    let new_context = { gamma = (x, a) :: gamma_var; inductive_types = gamma_ind; values = gamma_val } in
    debug ("tryna type pi " ^ x ^ ": " ^ (affiche_lam a) ^ " to " ^ (affiche_lam b));
    check_is_type gamma a;
    debug ("a was type, lets see if " ^ (affiche_lam (reduce new_context b)) ^ " is");
    check_is_type new_context b;
    Type 
  | Func(v, ty, body) ->
    debug ("tryna type func " ^ (affiche_lam ty) ^ " to " ^ (affiche_lam body));
    check_is_type gamma ty;
    debug "ty was type";
    let new_context = { gamma = (v, ty) :: gamma_var; inductive_types = gamma_ind; values = gamma_val } in
    let body_type = infer new_context body in
    debug (affiche_lam body_type);
    check_is_type new_context body_type;
    Pi(v, ty, body_type)
  | App(f, t) -> (
    match infer gamma (reduce gamma f) with
    | Pi(x, a, b) -> 
      typecheck gamma t a;
      reduce gamma (replace b x t)
    | _ -> 
      debug "Type error in an app";
      raise Type_error;
  )
  | Fst(t) -> (
    debug "tryna type fst";
    match infer gamma (reduce gamma t) with
    | Prod(a, _) -> a
    | _ ->
      debug "Type error in Fst";
      raise Type_error;
  )
  | Snd(t) -> (
    debug "tryna type snd";
    match infer gamma (reduce gamma t) with
    | Prod(_, b) -> b
    | _ ->
      debug "Type error in Snd";
      raise Type_error;
  )
  | Pair(t, t') -> (
    let a = infer gamma (reduce gamma t) in
    debug "typed first of pair";
    let b = infer gamma (reduce gamma t') in
    debug ("PAIR " ^ (affiche_lam (reduce gamma term)));
    Prod(a, b)
  )
  | Prod(t, t') -> (
    debug "tryna type prod";
    check_is_type gamma t;
    debug "typed first of prod";
    check_is_type gamma t';
    debug ("PROD " ^ (affiche_lam (reduce gamma term)));
    Type
  )
  | Sum(t, t') -> (
    debug "tryna type sum";
    check_is_type gamma t;
    debug "typed first of sum";
    check_is_type gamma t';
    debug ("SUM " ^ (affiche_lam (reduce gamma term)));
    Type
  )
  | InL(a, b) -> (
    debug "tryna type INL";
    check_is_type gamma b;
    Sum(infer gamma (reduce gamma a), b)
  )
  | InR(a, b) -> (
    debug "tryna type INR";
    check_is_type gamma a;
    Sum(a, infer gamma (reduce gamma b))
  )
  | Match(avb, a_c, b_c) -> (
    debug "tryna type match";
    match (infer gamma (reduce gamma avb), 
          infer gamma (reduce gamma a_c), 
          infer gamma (reduce gamma b_c)) with
    | Sum(a, b), Pi(x, a', c1), Pi(x', b', c2) -> (
      debug ("tryna type " ^ (affiche_lam (Sum(a, b))) ^ " @ " ^ (affiche_lam (Pi(x, a', c1))) ^ " @ " ^ (affiche_lam (Pi(x', b', c2))));
      check_is_type gamma a;
      debug "1";
      check_is_type gamma b;
      debug ("2 " ^ (affiche_lam a) ^ " | " ^ (affiche_lam a'));
      assert (equiv gamma (reduce gamma a) (reduce gamma a'));
      debug ("3 " ^ (affiche_lam b) ^ " | " ^ (affiche_lam b'));
      assert (equiv gamma (reduce gamma b) (reduce gamma b'));
      debug "4";
      assert (equiv gamma (reduce gamma c1) (reduce gamma c2));
      c1
    )
    | _ -> debug "Type error in match"; raise Type_error
  )
  | Inductive(i) -> (
    let (_name, arity, _constructors) = List.nth gamma_ind i in
    arity
  )
  | Recursor(i, args) -> (
    let (ind_name, _arity, _constructors) = List.nth gamma_ind i in
    let recursor_ty =
      try List.assoc (ind_name ^ "_rec") gamma_var
      with Not_found -> raise Type_error
    in

    let rec infer_spine ty remaining_args =
      match remaining_args with
      | [] -> ty
      | arg :: rest -> (
        match reduce gamma ty with
        | Pi(x, a, b) ->
          typecheck gamma arg a;
          infer_spine (replace b x arg) rest
        | _ -> raise Type_error
      )
    in

    infer_spine recursor_ty args
  )
  | Constructor(i, j, args) -> (
    let (_ind_name, _arity, constructors) = List.nth gamma_ind i in
    let (_ctor_name, ctor_ty) = List.nth constructors j in

    let rec infer_ctor ty remaining_args =
      match remaining_args with
      | [] -> ty
      | arg :: rest -> (
        match reduce gamma ty with
        | Pi(x, a, b) ->
          typecheck gamma arg a;
          infer_ctor (replace b x arg) rest
        | _ -> raise Type_error
      )
    in

    infer_ctor ctor_ty args
  )

(*
Checks that the type of term is ~_alpha-beta to ty
does nothing or raises an error
*)
and typecheck (gamma:context) (term:lambdaterm) (ty:lambdaterm) : unit =
  let type_of_term = infer gamma term in
  (*print_endline ("typed " ^ affiche_lam type_of_term ^ " | expecting " ^ affiche_lam ty);*)
  if equiv gamma type_of_term ty then
    ()
  else
    raise Type_error
;;

(*
Check whether name occurs free in term.
*)
let rec occurs_bound bound name term =
  match term with
  | Var x -> x = name && not (List.mem x bound)
  | Type -> false
  | Mvar _ -> false
  | Inductive(i) -> false
  | Recursor(i, args) -> List.exists (occurs_bound bound name) args
  | Constructor(i, j, args) -> List.exists (occurs_bound bound name) args
  | Goal (_, a) -> occurs_bound bound name a
  | Pi (x, a, b) ->
    occurs_bound bound name a || occurs_bound (x :: bound) name b
  | Func (x, a, b) ->
    occurs_bound bound name a || occurs_bound (x :: bound) name b
  | App (a, b) | Pair(a, b) | Prod(a, b) | Sum(a, b) | InL(a, b) | InR(a, b) ->
    occurs_bound bound name a || occurs_bound bound name b
  | Fst(a) | Snd(a) -> occurs_bound bound name a
  | Match(a, b, c) -> occurs_bound bound name a || occurs_bound bound name b || occurs_bound bound name c
;;

(*https://link.springer.com/content/pdf/10.1007/BFb0037116.pdf*)
(*
This takes an inductive type (destructed) and checks its wellformedness
*)
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
