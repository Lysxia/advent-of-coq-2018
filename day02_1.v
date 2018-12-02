From Coq Require Import
     List Arith Ascii String
     OrderedTypeEx FMapAVL
     extraction.ExtrOcamlIntConv.
Import ListNotations.

From SimpleIO Require
     IOMonad.

From ExtLib Require Import
     Structures.Monads.
Import MonadNotation.
Local Open Scope monad.

From advent Require Import lib.

Module Algorithm (Import OT : OrderedType.OrderedType).

Module Map := FMapAVL.Make OT.

Fixpoint collect_aux (xs : list t) (count : Map.t nat) :
  Map.t nat :=
  match xs with
  | [] => count
  | x :: xs =>
    match Map.find x count with
    | None => collect_aux xs (Map.add x 1 count)
    | Some n => collect_aux xs (Map.add x (1+n) count)
    end
  end.

Definition collect (xs : list t) : Map.t nat :=
  collect_aux xs (Map.empty nat).

Definition two_or_three (xs : list t) : bool * bool :=
  Map.fold (fun _ n tot =>
              (fst tot || (n =? 2), snd tot || (n =? 3))%bool)
           (collect xs)
           (false, false).

End Algorithm.

Module Import A := Algorithm Ascii_OT.

Section main.

Context {m : Type -> Type} `{Monad m}
        `{MonadI (list ascii) m} `{MonadO nat m} `{MonadFix m}.

Definition main : m unit :=
  mfix (fun loop '(twos, threes) =>
    oid <- read;;
    match oid with
    | Some id =>
      let tot := two_or_three id in
      loop (if fst tot then 1+twos else twos,
            if snd tot then 1+threes else threes)
    | None =>
      print (twos * threes)
    end) (0, 0).

End main.

Import SimpleIO.IOMonad.

Definition exec : io_unit := unsafe_run main.

Extraction "day02_1.ml" exec.
