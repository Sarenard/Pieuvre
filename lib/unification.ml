open! Expr
open Util

type lt = lambdaterm
type ty = lt

type mcontext = {
  values : (int, lambdaterm) Hashtbl.t;
  types : (int, lambdaterm) Hashtbl.t;
}
;;

let empty_mcontext : mcontext = {
  values = Hashtbl.create 16;
  types = Hashtbl.create 16;
}
;;

type lcontext = (string * lambdaterm) list
[@@deriving show]
;;

type globalenv = (string * lambdaterm) list
[@@deriving show]
;;

let pp_hashtbl pp_k pp_v fmt tbl =
  let first = ref true in
  Format.fprintf fmt "{";
  Hashtbl.iter (fun k v ->
    if !first then first := false else Format.fprintf fmt "; ";
    Format.fprintf fmt "%a: %a" pp_k k pp_v v
  ) tbl;
  Format.fprintf fmt "}"

let pp_mcontext fmt ctx =
  Format.fprintf fmt "{ values = %a; types = %a }"
    (pp_hashtbl Format.pp_print_int pp_lambdaterm) ctx.values
    (pp_hashtbl Format.pp_print_int pp_lambdaterm) ctx.types

(*
Returns if lt1 \delta\Sigma reduces in lt2 in the context mctx
*)    
let delta_sigma_reduce_t (lt1:lambdaterm) (lt2:lambdaterm) (mctx : mcontext) : bool =
  match lt2 with
  | Mvar(i) -> has_binding (mctx.values) i lt2
  | _ -> failwith "Wrong left argument for delta_sigma_reduce"
;;

(*
Returns if lt1 \delta\Sigma^weak reduces in lt2
*)
let rec delta_sigma_reduce_weak_t (lt1:lambdaterm) (lt2:lambdaterm) : bool =
  match (lt1, lt2) with
  | (t, t') when 
    delta_sigma_reduce_t t t' empty_mcontext 
    -> true
  | (App(t, u1), App(t', u2)) when 
    u1 = u2 && delta_sigma_reduce_weak_t t t' 
    -> true
  | _ -> false
;;

(*
Computes the \delta\Sigma^weak reduction of lt1 in the context mctx
*)
let delta_sigma_reduce (lt1 : lambdaterm) (mctx : mcontext) : lambdaterm =
  match lt1 with
  | Mvar i ->
    (match Hashtbl.find_opt mctx.values i with
    | Some v -> v
    | None -> lt1)
  | _ -> lt1
;;

(*
Computes the \delta\Sigma^weak reduction of lt1
*)
let rec delta_sigma_reduce_weak (lt1:lambdaterm) : lambdaterm =
  match lt1 with
  | App(t, u) -> App(delta_sigma_reduce_weak t, u)
  | _ -> delta_sigma_reduce lt1 empty_mcontext
;;



(*for tests*)
let unify_run () = 

  failwith "End of unify_run";
;;