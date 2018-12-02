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
