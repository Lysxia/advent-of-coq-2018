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

Import SimpleIO.

Definition polymer_length : list int -> int :=
  fun cs => int_of_nat (List.length (rev_react cs)).

Definition purge (i : int) : list int -> list int :=
  filter (fun c => int_neqb c i && negb (reactable c i))%bool.

Section main.

Context {m : Type -> Type} `{Monad m} `{MonadFix m}
        `{MonadI int m} `{MonadO int m}.

Definition minimum_in (f : int -> int) (i j : int) : m int :=
  mfix (fun self '(i, best) =>
    if int_eqb i j then
      ret best
    else
      let y := f i in
      let i' := (i + int_of_nat 1)%int in
      if int_lt y best then
        self (i', y)
      else
        self (i', best)) ((i + int_of_nat 1)%int, f i).

Definition main : m unit :=
  cs <- read_all;;
  z <- minimum_in (fun i => polymer_length (purge i cs))
    (int_of_n 65) (int_of_n 91);;
  print z.

End main.

Definition exe : io_unit := IO.unsafe_run main.
Extraction "day05_2.ml" exe.
