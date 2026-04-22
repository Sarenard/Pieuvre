open Lib
open Expr
open Interactive

let nom_fichier = ref ""

let recupere_entree () =
  Arg.parse (* ci-dessous les 3 arguments de Arg.parse : *)
    [
    ] (* la liste des options, vide *)
    (fun s -> nom_fichier := s) (* la fonction a declencher lorsqu'on recupere un string qui n'est pas une option : ici c'est le nom du fichier, et on stocke cette information dans la reference nom_fichier *)
    ""; (* le message d'accueil, qui est vide *)
  try
    let where_from = match !nom_fichier with
      | "" -> stdin
      | s -> open_in s in
    let lexbuf = Lexing.from_channel where_from in
    let parse () = Parser.main Lexer.token lexbuf in
    parse ()
  with e -> (
    Printf.printf "Asteriiiiiiiiiiiiiiix\n"; raise e
  )
;;

let run () =
  let saisie = recupere_entree () in
  print_endline (show_lambdaterm saisie);
  interactive saisie;
;;

let _ = run ()
