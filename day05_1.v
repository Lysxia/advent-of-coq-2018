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

Module Char.

Parameter lxor : int -> int -> int.
Extract Inlined Constant lxor => "Pervasives.(lxor)".

Parameter alphanum : int -> bool.
Extract Constant alphanum => "fun c -> c >= 65".

Definition reactable (c1 c2 : int) : bool :=
  int_eqb (lxor c1 c2)
          (int_of_nat 32).

End Char.

Section main.

Context {m : Type -> Type} `{Monad m} `{MonadFix m}
        `{MonadI int m} `{MonadO nat m}.

Definition main : m unit :=
  mfix (fun self stack =>
    oc <- read;;
    (* let done := for' (rev' stack) print in *)
    let done := print (List.length stack) in
    match oc with
    | None => done
    | Some c =>
      if Char.alphanum c then
        match stack with
        | [] => self [c]
        | c' :: stack' =>
          if Char.reactable c c' then
            self stack'
          else
            self (c :: stack)
        end
      else
        done
    end) [].

End main.

Instance MonadI_int_IO : MonadI int IO := {
  read := catch_eof (input_byte stdin);
}.

Instance MonadO_list_int_IO : MonadO int IO := {
  print := output_byte stdout;
}.

Definition exe : io_unit := IO.unsafe_run main.
Extraction "day05_1.ml" exe.
