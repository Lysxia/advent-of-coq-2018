(* The input for this one is assumed to be sorted (e.g., using
   the [sort] command). *)

From Coq Require Import
     List Arith NArith ZArith Ascii String
     OrderedTypeEx FSetAVL FMapAVL
     extraction.ExtrOcamlIntConv
     Lia.
Import ListNotations.

From SimpleIO Require
     IOMonad OcamlPervasives.

From ExtLib Require Import
     Structures.Monads.
Import MonadNotation.
Local Open Scope monad.

From advent Require Import lib.

(* Minutes since midnight. *)
Definition time : Type := N.

(* We assume shifts happen around midnight. *)
Variant event : Type :=
| Shift (guard : N)
| FallsAsleep
| WakesUp
.

Section main.

Context {m : Type -> Type} `{Monad m} `{MonadFix m}
        `{MonadI (time * event) m}
        `{MonadO N m}.

Definition main : m unit :=
  s <- read_all;;
  ret tt.

End main.

Module io.

Import SimpleIO.IOMonad SimpleIO.OcamlPervasives SimpleIO.Utils.
Import IONotations.

(* Partial function!? *)
Parameter parse_event : forall {TIME EVENT : Type},
    (int -> TIME) ->
    (int -> EVENT) -> EVENT -> EVENT ->
    ocaml_string -> TIME * EVENT.

Extract Constant parse_event =>
  "fun mk_time mk_shift sleep wakeup s ->
   try
     Scanf.sscanf s ""[1518-%_d-%_d %_d:%d] %[^\n]""
       (fun mn e ->
          (mk_time mn, match e with
               | ""falls asleep"" -> sleep
               | ""wakes up"" -> wakeup
               | _ -> Scanf.sscanf e ""Guard #%d"" mk_shift)
       )
   with End_of_file ->
    failwith (Printf.sprintf ""Parse error: %S"" s)".

Instance MonadI_event_IO : MonadI (time * event) IO := {
  read := catch_eof (
    s <- read_line';;
    ret (parse_event
           n_of_int
           (fun g => Shift (n_of_int g)) FallsAsleep WakesUp
           s));
}.

End io.

Import SimpleIO.IOMonad.
Import SimpleIO.CoqPervasives.

Definition exec : io_unit := unsafe_run main.
Extraction "day04_1.ml" exec.
