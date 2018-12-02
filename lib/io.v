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

From SimpleIO Require Import
     IOMonad CoqPervasives Utils.

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

Definition read_of_int {A : Type} (of_int : int -> A)
  : IO (option A) :=
  catch_eof (map_io of_int read_int).

Definition print_to_int {A : Type} (to_int : A -> int)
           (n : A) : IO unit :=
  print_int (to_int n);;
  print_newline.

Definition read_Z : IO (option Z) := read_of_int z_of_int.
Definition read_nat : IO (option nat) := read_of_int nat_of_int.

Definition print_Z : Z -> IO unit := print_to_int int_of_z.
Definition print_nat : nat -> IO unit := print_to_int int_of_nat.

End IO.

Instance MonadError_IO : MonadError IO := {
  error := IO.error;
}.

Instance MonadI_string_IO : MonadI string IO := {
  read := catch_eof read_line;
}.

Instance MonadI_list_ascii_IO : MonadI (list ascii) IO := {
  read := map_io (option_map list_of_string) read
}.

Instance MonadI_Z_IO : MonadI Z IO := {
  read := IO.read_Z;
}.

Instance MonadO_nat_IO : MonadO nat IO := {
  print := IO.print_nat;
}.

Instance MonadO_Z_IO : MonadO Z IO := {
  print := IO.print_Z;
}.
