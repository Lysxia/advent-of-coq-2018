From Coq Require Import
     Ascii String List OrderedType.
Import ListNotations.

(* Convert between strings and lists. *)

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | ""%string => []
  | String c s => c :: list_of_string s
  end.

Fixpoint string_of_list (cs : list ascii) : string :=
  match cs with
  | [] => ""%string
  | c :: cs => String c (string_of_list cs)
  end.

(* [ascii] as an [OrderedType]. *)

Class Ordered (T : Type) : Type := {
  lt : T -> T -> Prop;
}.

Class OrderedGood (T : Type) `{Ordered T} : Type := {
  lt_trans : forall t1 t2 t3, lt t1 t2 -> lt t2 t3 -> lt t1 t3;
  lt_not_eq : forall t1 t2, lt t1 t2 -> t1 <> t2;
}.

Class Comparable (T : Type) `{Ordered T} : Type := {
  compare : forall t1 t2, OrderedType.Compare lt eq t1 t2;
}.

Instance Ordered_bool : Ordered bool := {
  lt b1 b2 := b1 = false /\ b2 = true;
}.

Instance OrderedGood_bool : OrderedGood bool := {}.
Proof.
  - firstorder.
  - firstorder; subst; auto.
Qed.

Instance Comparable_bool : Comparable bool := {
  compare b1 b2 :=
    match b1, b2 return OrderedType.Compare _ _ b1 b2 with
    | true, true => EQ eq_refl
    | true, false => GT (conj eq_refl eq_refl)
    | false, true => LT (conj eq_refl eq_refl)
    | false, false => EQ eq_refl
    end
}.

Instance Ordered_pair (T1 T2 : Type)
         `{H1 : Ordered T1} `{H2 : Ordered T2} : Ordered (T1 * T2) := {
  lt p1 p2 := lt (fst p1) (fst p2) \/
              (fst p1 = fst p2 /\ lt (snd p1) (snd p2));
}.

Instance OrderedGood_pair (T1 T2 : Type)
         `{H1 : OrderedGood T1} `{H2 : OrderedGood T2} :
  OrderedGood (T1 * T2).
Proof.
  destruct H1 as [lt_trans1 lt_not_eq1], H2 as [lt_trans2 lt_not_eq2].
  constructor.
  { intros t1 t2 t3 [H12 | [H12 H12']] [H23 | [H23 H23']].
    - left; eapply lt_trans1; eauto.
    - left; rewrite <- H23; auto.
    - left; rewrite H12; auto.
    - right; split.
      + etransitivity; eauto.
      + eapply lt_trans2; eauto.
  }
  { intros t1 t2 [H12 | [H12 H12']] t_eq; subst.
    - eapply lt_not_eq1; eauto.
    - eapply lt_not_eq2; eauto.
  }
Qed.

Instance Comparable_pair (T1 T2 : Type)
         `{Comparable T1} `{Comparable T2} : Comparable (T1 * T2) := {
  compare t1 t2 :=
    match compare (fst t1) (fst t2) with
    | EQ Heq1 =>
      match compare (snd t1) (snd t2) with
      | EQ Heq2 => _
      | GT Hgt2 => _
      | LT Hlt2 => _
      end
    | GT Hgt1 => _
    | LT Hlt1 => _
    end;
}.
Proof.
  - firstorder.
  - firstorder.
  - apply EQ; destruct t1, t2; f_equal; auto.
  - apply GT; firstorder.
  - apply GT; firstorder.
Defined.

Definition tuple_of_ascii :=
  fun '(Ascii a b c d e f g h) => (a, b, c, d, e, f, g, h).

Lemma tuple_of_ascii_inj : forall t1 t2,
    tuple_of_ascii t1 = tuple_of_ascii t2 ->
    t1 = t2.
Proof.
  intros [] [] H; inversion H; auto.
Qed.

Module Ascii_OT <: OrderedType.OrderedType.
   Definition t : Type := ascii.
   Definition eq : t -> t -> Prop := eq.

   Definition lt : t -> t -> Prop :=
     fun t1 t2 => lt (tuple_of_ascii t1) (tuple_of_ascii t2).

   Definition eq_refl : forall x : t, eq x x := @eq_refl _.
   Definition eq_sym : forall x y : t, eq x y -> eq y x := @eq_sym _.
   Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z := @eq_trans _.

   Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
   Proof.
     intros [] [] [].
     apply lt_trans.
   Qed.

   Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
   Proof.
     intros [] [] lt_t eq_ascii.
     apply lt_not_eq in lt_t.
     apply lt_t.
     inversion eq_ascii; auto.
   Qed.

   Lemma compare : forall x y : t, OrderedType.Compare lt eq x y.
   Proof.
     intros t1 t2.
     destruct (compare (tuple_of_ascii t1) (tuple_of_ascii t2)).
     - apply LT. auto.
     - apply EQ. apply tuple_of_ascii_inj; auto.
     - apply GT. auto.
   Defined.

   Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
   Proof.
     intros t1 t2.
     destruct (compare t1 t2).
     - right. apply lt_not_eq; auto.
     - left; auto.
     - right. intro H; symmetry in H; apply lt_not_eq in H; auto.
   Defined.
End Ascii_OT.

Definition eqb_ascii (a b : ascii) : bool :=
  if Ascii_OT.eq_dec a b then true else false.

Lemma eqb_eq (a b : ascii) : eqb_ascii a b = true <-> a = b.
Proof.
  unfold eqb_ascii.
  destruct Ascii_OT.eq_dec; split; auto. discriminate.
Qed.

Lemma neqb_neq (a b : ascii) : eqb_ascii a b = false <-> a <> b.
Proof.
  rewrite <- eqb_eq, Bool.not_true_iff_false; reflexivity.
Qed.
