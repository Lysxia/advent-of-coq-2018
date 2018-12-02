From Coq Require Import
     List.
Import ListNotations.

Fixpoint find_some {A B : Type}
         (f : A -> option B) (xs : list A) : option B :=
  match xs with
  | [] => None
  | x :: xs =>
    match f x with
    | None => find_some f xs
    | Some y => Some y
    end
  end.

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
         (xs xs' : list A) : bool :=
  match xs, xs' with
  | [], [] => true
  | x :: xs, x' :: xs' =>
    eqb x x' && eqb_list eqb xs xs'
  | _, _ => false
  end.
