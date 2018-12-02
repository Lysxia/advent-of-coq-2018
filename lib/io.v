(* Interface for IO. *)

From Coq Require Import
     List ZArith String
     extraction.ExtrOcamlIntConv.
Import ListNotations.

From Coq.extraction Require Import
     ExtrOcamlIntConv.

From ExtLib Require Import
     Data.Monads.OptionMonad
     Structures.Monads.

From SimpleIO Require Import
     IOMonad CoqPervasives Utils.

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

(* Implementation *)

Instance Monad_IO : Monad IO := {
  Monad.ret := @IOMonad.ret;
  Monad.bind := @IOMonad.bind;
}.

Instance MonadFix_IO : MonadFix IO := {
  mfix := @fix_io;
}.

Module IO.

Import IONotations.

Definition error (a : Type) (s : string) : IO a :=
  prerr_endline s;; exit_nat 1.

Definition read_Z : IO (option Z) :=
  catch_eof (map_io z_of_int read_int).

Definition print_Z (z : Z) : IO unit :=
  print_int (int_of_z z);;
  print_newline.

End IO.

Instance MonadError_IO : MonadError IO := {
  error := IO.error;
}.

Instance MonadIZ_IO : MonadI Z IO := {
  read := IO.read_Z;
}.

Instance MonadOZ_IO : MonadO Z IO := {
  print := IO.print_Z;
}.
