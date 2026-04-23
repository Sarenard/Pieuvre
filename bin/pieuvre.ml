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
      interactive ();
    )
    | filename -> 
      let content = In_channel.with_open_text filename In_channel.input_all in 
      automatic content;
  ;
;;

let _ = run ()
