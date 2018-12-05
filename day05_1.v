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

From advent Require Import lib.

Import SimpleIO.

Parameter lxor : int -> int -> int.
Extract Inlined Constant lxor => "Pervasives.(lxor)".

Parameter alphanum : int -> bool.
Extract Constant alphanum => "fun c -> c >= 65".

Definition reactable (c1 c2 : int) : bool :=
  int_eqb (lxor c1 c2)
          (int_of_nat 32).

Definition react_f (stack : list int) (c : int) : list int :=
  if alphanum c then
    match stack with
    | [] => [c]
    | c' :: stack' =>
      if reactable c c' then
        stack'
      else
        c :: stack
    end
  else
    stack.

Section main.

Context {m : Type -> Type} `{Monad m} `{MonadFix m}
        `{MonadI int m} `{MonadO nat m}.

Definition main : m unit :=
  stack <- fold_read react_f [];;
  print (List.length stack).

End main.

Instance MonadI_int_IO : MonadI int IO := {
  read := catch_eof (input_byte stdin);
}.

Instance MonadO_list_int_IO : MonadO int IO := {
  print := output_byte stdout;
}.

Definition exe : io_unit := IO.unsafe_run main.
Extraction "day05_1.ml" exe.
