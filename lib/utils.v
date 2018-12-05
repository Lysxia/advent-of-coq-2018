From Coq Require Import
     List.
Import ListNotations.

From ExtLib Require Import
     Structures.Monad.

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

(* Properties *)

Lemma find_some_ex {A B : Type}
      (f : A -> option B) (xs : list A) (y : B) :
  find_some f xs = Some y -> exists x, In x xs /\ f x = Some y.
Proof.
  induction xs as [| x xs IH]; intros Hy.
  - inversion Hy.
  - simpl in Hy.
    destruct (f x) eqn:Hx.
    + exists x; inversion Hy; subst; firstorder.
    + destruct IH as [x' H']; auto.
      exists x'; firstorder.
Qed.

Lemma eqb_list_eq {A : Type}
      (eqb : A -> A -> bool)
      (eqb_eq : forall x y, eqb x y = true -> x = y) :
  forall xs ys, eqb_list eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys]; try discriminate.
  - reflexivity.
  - simpl; intros Hs.
    apply andb_prop in Hs.
    destruct Hs as [Hx Hxs].
    rewrite (eqb_eq x y) by apply Hx.
    rewrite (IH ys) by apply Hxs.
    reflexivity.
Qed.

Lemma iter_cons {A : Type} (a : A) (n : nat) (xs : list A) :
  PeanoNat.Nat.iter n (cons a) xs = repeat a n ++ xs.
Proof.
  induction n; simpl; auto.
  rewrite IHn; auto.
Qed.

Lemma repeat_nth1 {A : Type} (m n : nat) (a b : A) :
  m < n -> nth m (repeat a n) b = a.
Proof.
  generalize dependent n.
  induction m; intros; destruct n; auto; try solve [inversion H].
  apply IHm, Lt.lt_S_n; auto.
Qed.

Lemma repeat_nth2 {A : Type} (m n : nat) (a b : A) :
  n <= m -> nth m (repeat a n) b = b.
Proof.
  generalize dependent n.
  induction m; intros; destruct n; auto; try solve [inversion H].
  apply IHm, le_S_n; auto.
Qed.

Lemma nth_nil {A : Type} (n : nat) (a : A) :
  nth n [] a = a.
Proof.
  destruct n; auto.
Qed.

Lemma fold_left_hom {A B C}
      (f : A -> B -> A) (g : C -> B -> C) (h : A -> C) xs y :
  (forall a b, h (f a b) = g (h a) b) ->
  h (fold_left f xs y) = fold_left (fun a b => g a b) xs (h y).
Proof.
  intros.
  generalize dependent y.
  induction xs; auto; intros; simpl.
  rewrite IHxs, H; auto.
Qed.

Lemma fold_left_map {A B C} (f : A -> B -> A) (g : C -> B) xs y :
  fold_left (fun y x => f y (g x)) xs y = fold_left f (map g xs) y.
Proof.
  revert y.
  induction xs; auto; intros; simpl.
  rewrite IHxs; auto.
Qed.

Lemma fold_left_cons_1 {A : Type} (xs ys : list A) :
  fold_left (fun xs x => x :: xs) xs ys = rev xs ++ ys.
Proof.
  revert ys; induction xs; intros; simpl; auto.
  rewrite <- app_assoc; auto.
Qed.

Lemma fold_left_cons {A : Type} (xs : list A) :
  fold_left (fun xs x => x :: xs) xs [] = rev xs.
Proof.
  rewrite fold_left_cons_1. rewrite app_nil_r. reflexivity.
Qed.

(* Monadic stuff *)

(* TODO: send to ext-lib *)
Fixpoint for' {m : Type -> Type} `{Monad m} {A : Type}
         (xs : list A) (f : A -> m unit) : m unit :=
  match xs with
  | [] => ret tt
  | x :: xs => bind (f x) (fun _ => for' xs f)
  end.
