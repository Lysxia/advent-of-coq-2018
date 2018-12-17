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

From SimpleIO Require Import SimpleIO.

From advent.lib Require Import
     string.

Class MonadDebug (m : Type -> Type) : Type :=
  debug : IO unit -> m unit.

Arguments debug {m _}.

(* Keep this out of the instance database by default.
   It can be added using [Existing Instance MonadDebug_ignore]. *)
Definition MonadDebug_ignore m `{Monad m} : MonadDebug m :=
  fun _ => ret tt.

Class MonadError (m : Type -> Type) : Type :=
  error : forall a, string -> m a.

Arguments error {m _ a}.

(* Read inputs of type [I]. *)
Class MonadI (I : Type) (m : Type -> Type) : Type :=
  read : m (option I).

(* Print outputs of type [O]. *)
Class MonadO (O : Type) (m : Type -> Type) : Type :=
  print : O -> m unit.

(* Extra combinators *)

(* [fold_read] can be implemented using [mfix] (and we do so below),
   but there are some monads for which [fold_read] can be defined
   [mfix] cannot. Hence we make a type class to keep this general.
 *)
Class FoldRead (I : Type) (m : Type -> Type) : Type :=
  fold_read : forall (S : Type), (S -> I -> S) -> S -> m S.

Arguments fold_read {I m FoldRead S}.

Section Combini.
Import MonadNotation.
Open Scope monad.

Context {I : Type} {m : Type -> Type} `{Monad m}.

Section DefFoldRead.
Context `{MonadFix m} `{MonadI I m}.

(* Consume all input with a fold. *)
Global Instance FoldRead_MonadFix : FoldRead I m :=
  fun {S : Type} (f : S -> I -> S) (s0 : S) =>
  mfix (fun loop s =>
    ox <- read;;
    match ox with
    | None => Monad.ret s
    | Some x => loop (f s x)
    end) s0.

End DefFoldRead.

Section DefReadAll.
Context `{FoldRead I m}.

Definition read_all : m (list I) :=
  ys <- fold_read (fun xs x => x :: xs) [];;
  ret (rev' ys).

End DefReadAll.

End Combini.

(* Implementation *)

Module IO.

Import IO.Notations.

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

Instance MonadDebug_IO : MonadDebug IO :=
  fun x => x.

Instance MonadI_string_IO : MonadI string IO := {
  read := catch_eof read_line';
}.

Instance MonadI_list_ascii_IO : MonadI (list ascii) IO := {
  read := IO.map (option_map list_of_string) read
}.

Instance MonadI_ocaml_string_IO : MonadI ocaml_string IO := {
  read := catch_eof read_line;
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
  print := print_endline;
}.

End IO.
