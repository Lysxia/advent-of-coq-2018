From Coq Require Import
     List ZArith Ascii String Streams
     OrderedTypeEx FSetAVL
     extraction.ExtrOcamlIntConv.
Import ListNotations.

From SimpleIO Require
     IOMonad CoqPervasives.

From ExtLib Require Import
     Structures.Monads.
Import MonadNotation.
Local Open Scope monad.

From advent Require Import lib.

Module ZSet := FSetAVL.Make Z_as_OT.

Definition cycle_aux {A} (self : Stream A) : list A -> Stream A :=
  cofix cycle_aux (xs : list A) : Stream A :=
    match xs with
    | [] => self
    | x :: xs => Cons x (cycle_aux xs)
    end.

Definition cycle {A} (xs : list A) : option (Stream A) :=
  match xs with
  | [] => None
  | x :: xs => Some (cofix res := Cons x (cycle_aux res xs))
  end.

Section main.

Context {m : Type -> Type}
        `{Monad m} `{MonadError m}
        `{MonadIOZ m} `{MonadFix m}.

Definition parse_stream : m (Stream Z) :=
  mfix (fun loop acc =>
    oz <- read_Z;;
    match oz with
    | None =>
      match cycle (rev acc) with
      | None => error "empty input"
      | Some s => ret s
      end
    | Some z => loop (z :: acc)
    end) [].

Definition no_seen : ZSet.t := ZSet.empty.

Definition search (s : Stream Z) : m Z :=
  mfix (fun loop '(seen, pos, (Cons z s)) =>
    if ZSet.mem pos seen then
      ret pos
    else
      loop (ZSet.add pos seen, (pos + z)%Z, s)
  ) (no_seen, 0%Z, s).

Definition main : m unit :=
  s <- parse_stream;;
  z <- search s;;
  print_Z z.

End main.

Import SimpleIO.IOMonad.

Definition exec : io_unit := unsafe_run main.

Extraction "day01_2.ml" exec.

