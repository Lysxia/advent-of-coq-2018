From Coq Require Import
     List Streams.
Import ListNotations.

Fixpoint Str_take {A : Type} (n : nat) (xs : Stream A) : list A :=
  match n, xs with
  | O, _ => []%list
  | S n, Cons x xs => x :: Str_take n xs
  end.

CoFixpoint Str_scanl {A B : Type}
           (f : B -> A -> B) (y : B) (xs : Stream A) : Stream B :=
  Cons y (match xs with
          | Cons x xs => Str_scanl f (f y x) xs
          end).

(* Properties *)

Lemma Str_nth_S {A : Type} (n : nat) (xs : Stream A) :
  Str_nth (S n) xs = Str_nth n (tl xs).
Proof. auto. Qed.

Lemma Str_nth_tl_S {A : Type} (n : nat) (xs : Stream A) :
  Str_nth_tl (S n) xs = tl (Str_nth_tl n xs).
Proof.
  revert xs; induction n; auto; intros.
  simpl; rewrite <- IHn; auto.
Qed.

Lemma Str_take_S {A : Type} (n : nat) (xs : Stream A) :
  Str_take (S n) xs = Str_take n xs ++ [Str_nth n xs].
Proof.
  revert xs; induction n; intros []; auto.
  simpl; rewrite <- IHn; auto.
Qed.

Lemma Str_scanl_S {A B : Type} (n : nat) (f : B -> A -> B)
      (y : B) (xs : Stream A) :
  Str_nth (S n) (Str_scanl f y xs) =
  f (Str_nth n (Str_scanl f y xs)) (Str_nth n xs).
Proof.
  revert xs; revert y; induction n; intros; destruct xs; cbn; auto.
  - repeat rewrite Str_nth_S; simpl. rewrite <- IHn; auto.
Qed.

Lemma Str_scanl_nth {A B : Type}
      (f : B -> A -> B) (y : B) (xs : Stream A)
      (n : nat) :
  Str_nth n (Str_scanl f y xs) = fold_left f (Str_take n xs) y.
Proof.
  revert xs. revert y.
  induction n; intros; destruct xs as [x xs].
  - auto.
  - simpl; rewrite <- IHn; auto.
Qed.
