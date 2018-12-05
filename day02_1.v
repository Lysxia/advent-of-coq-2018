Set Warnings "-extraction-opaque-accessed".

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

Module Algorithm (Import OT : OrderedType.OrderedType).

Module Map := FMapAVL.Make OT.

(* Interpret a finite map [Map.t nat] as a function [t -> nat],
   defaulting to 0 outside of its support. *)
Definition lookup (count : Map.t nat) : t -> nat :=
  fun x : t =>
    match Map.find x count with
    | None => 0
    | Some n => n
    end.

(* Increment the value associated to [x] by one. *)
Definition increment (x : t) : Map.t nat -> Map.t nat :=
  fun count => Map.add x (1 + lookup count x) count.

(* [collect xs] gives, for every element [x : t], the number
   of times it occues in [xs]. *)
Definition collect (xs : list t) : Map.t nat :=
  fold_left
    (fun count x => increment x count)
    xs
    (Map.empty nat).

(* Now it is straightforward to determine whether some element
   occurs two or three times in the list [xs]. *)
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

(* We have two counters for the numbers of words containing
   two/three of any letter. For each word, [two_or_three] tells us
   whether to increment each counter. *)
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

Import SimpleIO.

Definition exec : io_unit := IO.unsafe_run main.

Extraction "day02_1.ml" exec.

Section spec.

(* We first formalize the property of having exactly two/three
   of a given letter. *)

(* The number of occurences of [c] in [xs]. *)
Definition n_occurs (c : ascii) (xs : list ascii) : nat :=
  List.length (filter (eqb_ascii c) xs).

(* [has_n n xs : Prop] holds when some letter appears in [xs]
   exactly [n] times. *)
Definition has_n (n : nat) (xs : list ascii) : Prop :=
  exists c, n_occurs c xs = n.

Definition has_two : list ascii -> Prop := has_n 2.
Definition has_three : list ascii -> Prop := has_n 3.

(* The meat of the program: [two_or_three].

   We first state the specification of [two_or_three], and then prove
   properties about the surrounding auxiliary functions until
   we can prove that spec. *)

(* The two booleans of [two_or_three] tell us whether there are
   elements occuring two/three times in the list [xs]. *)
Definition two_or_three_spec : Prop :=
  forall xs : list ascii,
    (fst (two_or_three xs) = true <-> has_two xs) /\
    (snd (two_or_three xs) = true <-> has_three xs).

Lemma increment_plus_one x count :
  lookup (increment x count) x = S (lookup count x).
Proof.
  unfold increment, lookup.
  destruct (Map.find x count) as [n |] eqn:e_find.
  - apply Map.find_2 in e_find.
    erewrite Map.find_1; [eauto |].
    apply Map.add_1; auto.
  - erewrite Map.find_1; [eauto |].
    apply Map.add_1; auto.
Qed.

Lemma Map_find_None {A : Type} y (m : Map.t A) :
  (forall e, ~ Map.MapsTo y e m) <-> Map.find y m = None.
Proof.
  split.
  - intros H. destruct Map.find as [a | ] eqn:e_find; auto.
    apply Map.find_2 in e_find. firstorder.
  - intros H e HM. apply Map.find_1 in HM.
    rewrite HM in H. discriminate.
Qed.

Lemma Map_add_neq {A : Type} (m : Map.t A) (x y : Map.key) (e e' : A) :
  x <> y -> (Map.MapsTo y e (Map.add x e' m) <-> Map.MapsTo y e m).
Proof.
  split. { apply Map.add_3; auto. } { apply Map.add_2; auto. }
Qed.

Lemma Map_find_add_neq  {A : Type} (m : Map.t A) x y e :
  x <> y -> Map.find y (Map.add x e m) = Map.find y m.
Proof.
  intros Hneq.
  destruct (Map.find y m) as [e' |] eqn:e_find.
  - apply Map.find_1, Map.add_2, Map.find_2; auto.
  - apply Map_find_None.
    intros e' HM.
    apply Map.add_3 in HM; auto.
    apply Map.find_1 in HM.
    rewrite HM in e_find. discriminate.
Qed.

Lemma increment_id x y count :
  x <> y -> lookup (increment x count) y = lookup count y.
Proof.
  intro Hneq.
  unfold increment, lookup.
  destruct (Map.find y count) as [n |] eqn:e_find.
  - erewrite Map.find_1; [eauto |].
    apply Map.add_2; auto.
    apply Map.find_2; auto.
  - rewrite Map_find_add_neq; auto.
    rewrite e_find; auto.
Qed.

(* A translation and proof of the specification of [collect]
   stated earlier. *)
Lemma collect_correct :
  forall xs c, lookup (collect xs) c = n_occurs c xs.
Proof.
  unfold collect.
  assert (H : forall xs c (count : Map.t nat),
             lookup (fold_left
               (fun count x => increment x count)
               xs
               count) c = n_occurs c xs + lookup count c).
  { induction xs as [| x xs]; simpl; auto.
    intros c count.
    unfold n_occurs. simpl.
    destruct eqb_ascii eqn:e_cx.
    - apply eqb_eq in e_cx; subst.
      simpl.
      rewrite <- Nat.add_succ_r.
      rewrite <- increment_plus_one.
      apply IHxs.
    - rewrite neqb_neq in e_cx.
      erewrite <- (increment_id _ _ count); eauto.
  }
  intros.
  specialize (H xs c (Map.empty nat)); unfold lookup in H; simpl in H.
  rewrite plus_0_r in H.
  auto.
Qed.

Lemma fold_left_ind {A B : Type} (P : list A -> B -> B -> Prop)
      (f : B -> A -> B)
      (Hnil : forall y, P [] y y)
      (Hcons : forall x xs y y', P xs (f y x) y' -> P (x :: xs) y y') :
  forall xs y,
    P xs y (fold_left f xs y).
Proof.
  induction xs as [| x xs]; auto.
  simpl; firstorder.
Qed.

Theorem two_or_three_correct : two_or_three_spec.
Proof.
  intro xs.
  remember (two_or_three xs) as ttx eqn:ettx.
  unfold two_or_three in ettx.
  rewrite Map.fold_1 in ettx.
  match type of ettx with
  | (_ = fold_left ?f _ _) =>
    assert (H : forall xs y,
               (fst (fold_left f xs y) = true <->
                (exists c, List.In (c, 2) xs) \/ fst y = true))
  end.
  { clear.
    induction xs; intros [t1 t2].
    - firstorder.
    - simpl. split.
      + intro H0.
        apply IHxs in H0. simpl in H0.
        destruct H0 as [[c H0] | H0].
        * firstorder.
        * apply Bool.orb_prop in H0.
          destruct H0; auto.
          rewrite Nat.eqb_eq in H.
          destruct a as [c p]; left; exists c. auto.
      + intros H0. apply IHxs.
        destruct H0 as [[c [H | H]]| H].
        * subst a; auto. simpl. rewrite Bool.orb_true_r; auto.
        * left. exists c; auto.
        * subst; auto.
  }
  split.
  - subst ttx. rewrite H.
    split.
    + intros [[c Hc]|]; [| discriminate].
      exists c.
      rewrite <- collect_correct.
      unfold lookup.
      erewrite Map.find_1; auto.
      apply Map.elements_2, SetoidList.In_InA; auto.
      typeclasses eauto.
    + intros [c Hc]. left.
      rewrite <- collect_correct in Hc.
      unfold lookup in Hc.
      destruct Map.find eqn:ec in Hc; [| discriminate].
      exists c.
      apply Map.find_2 in ec.
      apply Map.elements_1 in ec.
      apply SetoidList.InA_alt in ec.
      destruct ec as [[c' n'] []].
      inversion H0; simpl in *; subst; auto.
  - admit.
Abort.

End spec.
