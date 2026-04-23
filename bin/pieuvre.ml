open Lib
open Interactive
open Automatic

let nom_fichier = ref ""

let run () =
  Arg.parse
    [
      (*TODO :*)
      (*-reduce*)
      (*-alpha*)
      (*-typecheck*)
    ] 
    (*TODO : faire des trucs différents selon si on a un fichier ou pas*)
    (fun s -> nom_fichier := s)
    "";
  match !nom_fichier with
    | "" -> (
      (*interactive*)
      try
        let lexbuf = Lexing.from_channel stdin in
        let parse () = Parser.main Lexer.token lexbuf in
        interactive (parse ());
      with e -> (
        Printf.printf "Asteriiiiiiiiiiiiiiix\n"; raise e
      )
    )
    | filename -> 
      let lines = In_channel.with_open_text filename In_channel.input_lines in 
      automatic lines;
  ;
;;

let _ = run ()
