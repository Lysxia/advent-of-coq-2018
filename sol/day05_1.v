Set Warnings "-extraction-opaque-accessed".

From Coq Require Import
     Ascii String List Arith
     OrderedTypeEx FMapAVL
     extraction.ExtrOcamlIntConv.
Import ListNotations.

From SimpleIO Require SimpleIO.

From ExtLib Require Import
     Structures.Monads.
Import MonadNotation.
Local Open Scope monad.

From advent Require Import lib sol.day05_common.

Section main.

Context {m : Type -> Type} `{Monad m}
        `{FoldRead int m} `{MonadO nat m}.

Definition main : m unit :=
  stack <- fold_read react_f [];;
  print (List.length stack).

End main.

Import SimpleIO.
Definition exe : io_unit := IO.unsafe_run main.
Extraction "day05_1.ml" exe.

Section spec.

End spec.
