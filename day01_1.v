From Coq Require Import
     List ZArith Ascii String.
Import ListNotations.

From Coq.extraction Require Import
     ExtrOcamlIntConv.

From SimpleIO Require
     IOMonad.

From ExtLib Require Import
     Structures.Monads.
Import MonadNotation.
Local Open Scope monad.

From advent Require Import lib.

Section main.

Context {m : Type -> Type} `{Monad m}
        `{MonadIOZ m} `{MonadFix m}.

Definition main : m unit :=
  mfix (fun loop z0 =>
    oz <- read_Z;;
    match oz with
    | None => print_Z z0
    | Some z => loop (z + z0)%Z
    end) 0%Z.

End main.

Import SimpleIO.IOMonad.

Definition exec : io_unit := unsafe_run main.

Extraction "day01_1.ml" exec.

(**)

(* Functional spec. *)
Fixpoint sum_Z (zs : list Z) : Z :=
  match zs with
  | [] => 0
  | z :: zs => z + sum_Z zs
  end.
