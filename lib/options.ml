open Expr
open Util

(*
The -alpha option of the executable
usage : -reduce <filename>
action : takes (in a file) lt1&lt2, and prints if they are alpha-equivalents or not
*)
let alpha_opt (content:string) : unit =
  match List.map String.trim (String.split_on_char '&' content) with
  | [left; right] ->
    let lt_left = parse_type left in
    let lt_right = parse_type right in
    print_endline (string_of_bool (alpha lt_left lt_right))
  | _ ->
    failwith "Wrongly formed -alpha arguments"
;;

(*
The -reduce option of the executable
usage : -reduce <filename>
action : takes (in a file) a lt and prints the series of its reductions
*)
let reduce_opt (content:string) : unit =
  let lt = parse_type_dot content in
  let ctx = empty_env () in
  let current = ref lt in
  let stop = ref false in
  print_endline (affiche_lam !current);
  while not (!stop) do
    match betastep ctx !current with
    | Some next ->
      current := next;
      print_endline (affiche_lam !current)
    | None ->
      stop := true
  done
;;

(*
The -typecheck option of the executable
usage : -typecheck <filename>
action : takes (in a file) a statement t : T. and prints if t has type T
*)
let typecheck_opt (content:string) : unit =
  let (term, ty) = parse_typecheck content in
  let ctx = empty_env () in
  try
    check_is_type ctx ty;
    typecheck ctx term ty;
    print_endline "true"
  with
  | Type_error -> print_endline "false"
  | Unbound_variable _ -> print_endline "false"
;;
