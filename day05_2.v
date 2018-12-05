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

Fixpoint react (stack cs : list int) : list int :=
  match cs with
  | [] => stack
  | c :: cs =>
    match stack with
    | [] => react [c] cs
    | c' :: stack' =>
      if reactable c c' then
        react stack' cs
      else
        react (c :: stack) cs
    end
  end.

Definition react0 : list int -> list int := react [].

Definition polymer_length : list int -> int :=
  fun cs => int_of_nat (List.length (react0 cs)).

Definition purge (i : int) : list int -> list int :=
  filter (fun c => int_neqb c i && negb (reactable c i))%bool.

End Char.

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
  z <- minimum_in (fun i => Char.polymer_length (Char.purge i cs))
    (int_of_n 65) (int_of_n 91);;
  print z.

End main.

Instance MonadI_int_IO : MonadI int IO := {
  read :=
    ox <- catch_eof (input_byte stdin);;
    match ox with
    | None => ret None
    | Some x => ret (if Char.alphanum x then Some x else None)
    end;
}.

Instance MonadO_int_IO : MonadO int IO := {
  print n := print_int n;; print_newline
}.

Definition exe : io_unit := IO.unsafe_run main.
Extraction "day05_2.ml" exe.
