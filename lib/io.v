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

Class MonadIOZ (m : Type -> Type) : Type := {
  read_Z : m (option Z);
  print_Z : Z -> m unit;
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

Instance MonadIOZ_IO : MonadIOZ IO := {
  read_Z := IO.read_Z;
  print_Z := IO.print_Z;
}.
