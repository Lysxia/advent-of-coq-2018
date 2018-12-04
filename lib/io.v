(* Interface for IO. *)

From Coq Require Import
     List ZArith Ascii String
     extraction.ExtrOcamlIntConv.
Import ListNotations.

From Coq.extraction Require Import
     ExtrOcamlIntConv.

From ExtLib Require Import
     Data.Monads.OptionMonad
     Structures.Monads.

From SimpleIO Require Import RawChar.

From advent.lib Require Import
     string.

Class MonadError (m : Type -> Type) : Type := {
  error : forall a, string -> m a;
}.

Arguments error {m _ a}.

(* Read inputs of type [I]. *)
Class MonadI (I : Type) (m : Type -> Type) : Type := {
  read : m (option I);
}.

(* Print outputs of type [O]. *)
Class MonadO (O : Type) (m : Type -> Type) : Type := {
  print : O -> m unit;
}.

(* Extra combinators *)

Section Combini.
Import MonadNotation.
Open Scope monad.

Definition read_all {I : Type} {m : Type -> Type}
           `{Monad m} `{MonadI I m} `{MonadFix m} : m (list I) :=
  mfix (fun loop xs =>
    ox <- read;;
    match ox with
    | None => Monad.ret (rev' xs)
    | Some x => loop (x :: xs)
    end) [].

End Combini.

(* Implementation *)

Module IO.

Import IO.Notations.

Instance Monad_IO : Monad IO := {
  Monad.ret := @IO.ret;
  Monad.bind := @IO.bind;
}.

Instance MonadFix_IO : MonadFix IO := {
  mfix := @IO.fix_io;
}.

Definition error (a : Type) (s : string) : IO a :=
  prerr_endline s;; exit_nat 1.

Definition read_of_int {A : Type} (of_int : int -> A)
  : IO (option A) :=
  catch_eof (IO.map of_int read_int).

Definition print_to_int {A : Type} (to_int : A -> int)
           (n : A) : IO unit :=
  print_int (to_int n);;
  print_newline.

Instance MonadError_IO : MonadError IO := {
  error := IO.error;
}.

Instance MonadI_string_IO : MonadI string IO := {
  read := catch_eof read_line;
}.

Instance MonadI_list_ascii_IO : MonadI (list ascii) IO := {
  read := IO.map (option_map list_of_string) read
}.

Instance MonadI_N_IO : MonadI N IO := {
  read := read_of_int n_of_int;
}.

Instance MonadI_Z_IO : MonadI Z IO := {
  read := read_of_int z_of_int;
}.

Instance MonadI_nat_IO : MonadI nat IO := {
  read := read_of_int nat_of_int;
}.

Instance MonadO_N_IO : MonadO N IO := {
  print := print_to_int int_of_n;
}.

Instance MonadO_nat_IO : MonadO nat IO := {
  print := print_to_int int_of_nat;
}.

Instance MonadO_Z_IO : MonadO Z IO := {
  print := print_to_int int_of_z;
}.

Instance MonadO_string_IO : MonadO string IO := {
  print := print_endline;
}.

Instance MonadO_list_ascii_IO : MonadO (list ascii) IO := {
  print := fun s => print_endline (string_of_list s);
}.

Instance MonadO_ocaml_string_IO : MonadO ocaml_string IO := {
  print := print_endline';
}.

End IO.
