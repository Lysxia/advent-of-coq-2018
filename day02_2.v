From Coq Require Import
     List Arith Ascii String
     OrderedTypeEx FMapAVL
     extraction.ExtrOcamlIntConv.
Import ListNotations.

From SimpleIO Require SimpleIO.

From ExtLib Require Import
     Structures.Monads.
Import MonadNotation.
Local Open Scope monad.

From advent Require Import lib.

Section algorithm.

Context {A : Type} (eqb : A -> A -> bool).

(* [distance_one eqb xs xs']: when [xs] and [xs'] differ on
   exactly one element at the same position, the result is the list
   of elements common to [xs] and [xs'], in order. *)

Fixpoint distance_one_aux
         (acc : list A) (xs xs' : list A) : option (list A) :=
  match xs, xs' with
  | x :: xs, x' :: xs' =>
    if eqb x x' then
      distance_one_aux (x :: acc) xs xs'
    else if eqb_list eqb xs xs' then
      Some (rev acc ++ xs)
    else
      None
  | _, _ => None
  end.

Definition distance_one (xs xs' : list A) : option (list A) :=
  distance_one_aux [] xs xs'.

Fixpoint search (xss : list (list A)) : option (list A) :=
  match xss with
  | [] => None
  | xs :: xss =>
    match find_some (distance_one xs) xss with
    | Some ys => Some ys
    | None => search xss
    end
  end.

End algorithm.

Section main.

Context {m : Type -> Type} `{Monad m} `{MonadError m}
        `{MonadI (list ascii) m} `{MonadO (list ascii) m}
        `{MonadFix m}.

Definition main : m unit :=
  ids <- read_all;;
  match search eqb_ascii ids with
  | Some s => print s
  | None => error "Close IDs not found"
  end.

End main.

Import SimpleIO.IOMonad.

Definition exec : io_unit := IO.unsafe_run main.

Extraction "day02_2.ml" exec.
