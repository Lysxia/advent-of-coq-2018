From Coq Require Import
     List Streams.
Import ListNotations.

CoFixpoint Str_scanl {A B : Type}
           (f : B -> A -> B) (y : B) (xs : Stream A) : Stream B :=
  Cons y (match xs with
          | Cons x xs => Str_scanl f (f y x) xs
          end).

Fixpoint Str_take {A : Type} (n : nat) (xs : Stream A) : list A :=
  match n, xs with
  | O, _ => []%list
  | S n, Cons x xs => x :: Str_take n xs
  end.

Lemma scan_nth {A B : Type}
      (f : B -> A -> B) (y : B) (xs : Stream A)
      (n : nat) :
  Str_nth n (Str_scanl f y xs) = fold_left f (Str_take n xs) y.
Proof.
  revert xs. revert y.
  induction n; intros; destruct xs as [x xs].
  - auto.
  - simpl; rewrite <- IHn; auto.
Qed.
