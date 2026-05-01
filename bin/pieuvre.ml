open Lib
open! Interactive
open Automatic
open Unification

let nom_fichier = ref ""

let run () =
  Arg.parse
    [
      (*TODO (flags) :*)
      (*-reduce*)
      (*-alpha*)
      (*-typecheck*)
    ] 
    (fun s -> nom_fichier := s)
    "";
  match !nom_fichier with
    | "" -> (
      unify_run ();
      (*Interactive UI*)
      interactive ();
    )
    | filename -> 
      (*We treat the given file linearly*)
      let content = In_channel.with_open_text filename In_channel.input_all in 
      automatic content;
  ;
;;

let _ = run ()
