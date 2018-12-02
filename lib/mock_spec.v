(* Failed attempts at defining specifications on mocked programs.
   Damn [mfix].
 *)

From Coq Require Import
     List ZArith
     extraction.ExtrOcamlIntConv.
Import ListNotations.

From Coq.extraction Require Import
     ExtrOcamlIntConv.

From ExtLib Require Import
     Data.Monads.OptionMonad
     Structures.Monads.

From advent.lib Require Import
     io mock.

(* partial correctness *)
Module fuel_partial.

Definition spec' {a : Type}
           (m : fuelT (mock Prop) a)
           (i : input)
           (post : input -> Prop) (o : output) (x : a) : Prop :=
  forall fuel,
    un_mock (m fuel) (fun ox' i' o' =>
                        forall x', ox' = Some x' ->
                                   x' = x /\
                                   post i' /\
                                   o' = o) i.

Lemma spec_fix {a b} gf i (post : input -> Prop) o (x : a) (y : b) :
  spec' (gf (mfix gf) x) i post o y ->
  spec' (mfix gf x) i post o y.
Proof.
  intros Hspec fuel.
Abort.

End fuel_partial.

Module fuel.

Definition spec' {a : Type}
           (m : fuelT (mock Prop) a)
           (i : input)
           (post : input -> Prop) (o : output) (x : a) : Prop :=
  exists min_fuel,
    forall (P : _ -> _ -> _ -> Prop) fuel,
      fuel >= min_fuel ->
      (forall x' i' o',
          x' = Some x /\ post i' /\ o' = o -> P x' i' o') ->
      un_mock (m fuel) P i.

Definition spec (m : fuelT (mock Prop) unit) (i : input) (o : output) : Prop :=
  exists min_fuel,
    forall fuel,
      fuel >= min_fuel ->
      un_mock (m fuel) (fun x' i' o' =>
                             x' = Some tt /\ o' = o) i.

Lemma unfold_spec m i o :
  spec' m i (fun _ => True) o tt ->
  spec m i o.
Proof.
  intros [min_fuel Hspec'].
  exists min_fuel.
  intros fuel Hfuel.
  apply Hspec'; auto.
  firstorder.
Qed.

Lemma strong_post {a} m i (post1 post2 : input -> Prop) o (x : a) :
  (forall i', post1 i' -> post2 i') ->
  spec' m i post1 o x ->
  spec' m i post2 o x.
Proof.
  intros Hpost [min_fuel Hspec'].
  exists min_fuel. intros P fuel Hfuel HP.
  apply Hspec'; auto.
  firstorder.
Qed.

Lemma spec_fix {a b} gf i (post : input -> Prop) o (x : a) (y : b) :
  spec' (gf (mfix gf) x) i post o y ->
  spec' (mfix gf x) i post o y.
Proof.
  intros [min_fuel Hspec].
  exists (S min_fuel); intros P fuel Hfuel HP.
  induction fuel.
  - inversion Hfuel.
  - simpl.
Abort.

End fuel.

(* Interpret the CPS-style [mock] as a predicate transformer. *)
Module wp.

Notation wp := (mock Prop).

Definition incl_wp {a : Type} (m1 m2 : wp a) : Prop :=
  forall q i, un_mock m1 q i -> un_mock m2 q i.

Notation GF_wp a b := ((a -> wp b) -> (a -> wp b)).

(*
Definition mfix_wp {a b : Type}
          (gf : GF_wp a b)
          (x : a)
          (q : b -> input -> output -> Prop)
          (i : input) : Prop :=
  forall
    (P : a -> mock Prop b)
    (P_ind : forall y, incl_wp (P y) (gf P y)),
    un_mock (P x) q i.
*)

Variant mfix_wp {a b : Type}
          (gf : GF_wp a b)
          (x : a)
          (q : b -> input -> output -> Prop)
          (i : input) : Prop :=
| MWP
    (P : a -> mock Prop b)
    (PHolds : un_mock (P x) q i)
    (P_ind :forall y, incl_wp (P y) (gf P y))
.

Global Instance MonadFix_mock_Prop : MonadFix wp := {
  mfix _ _ gf x := Mk_mock (mfix_wp gf x)
}.

Definition monotonic_wp {a b : Type}
           (gf : GF_wp a b) :=
  forall m1 m2,
    (forall x, incl_wp (m1 x) (m2 x)) ->
    (forall x, incl_wp (gf m1 x) (gf m2 x)).

Theorem mfix_incl_1 {a b : Type}
        (gf : GF_wp a b)
        (gf_mon : monotonic_wp gf)
        (x : a) :
  incl_wp (mfix gf x) (gf (mfix gf) x).
Proof.
  intros q i [P PHolds P_ind]; simpl.
  eapply gf_mon.
  - unfold incl_wp; simpl.
    intros.
    econstructor.
    + eauto.
    + apply P_ind.
  - apply P_ind; auto.
Qed.

(*
Theorem mfix_incl_1 {a b : Type}
        (gf : GF_mp a b)
        (gf_mon : monotonic_mp gf)
        (x : a) :
  incl_mp (mfix gf x) (gf (mfix gf) x).
Proof.
  intros q i [P PHolds P_ind]; simpl.
  eapply gf_mon.
  - unfold incl_mp; simpl.
    intros.
    econstructor.
    + eauto.
    + apply P_ind.
  - apply P_ind; auto.
Qed.
*)

Theorem mfix_incl_2 {a b : Type}
        (gf : GF_wp a b)
        (gf_mon : monotonic_wp gf)
        (x : a) :
  incl_wp (gf (mfix gf) x) (mfix gf x).
Proof.
  intros q i H.
  econstructor.
  - eapply H.
  - intros x' q' i'. intro.
    eapply gf_mon; eauto.
Abort.

End wp.
