Set Warnings "-extraction-opaque-accessed".

From Coq Require Import
     Ascii String List Arith
     OrderedTypeEx FMapAVL
     Sets.Relations_3_facts
     Relations.Relations
     extraction.ExtrOcamlIntConv.
Import ListNotations.

From SimpleIO Require SimpleIO.

From ExtLib Require Import
     Structures.Monads.
Import MonadNotation.
Local Open Scope monad.

From advent Require Import lib.

Import SimpleIO.

(* Byte-by-byte input. *)
Instance MonadI_int_IO : MonadI int IO := {
  read :=
    (* Stop reading at the first newline. *)
    c <- input_byte stdin;;
    ret (if (c =? int_of_nat 10)%int then
           None
         else
           Some c);
}.

(* For debugging *)
Instance MonadO_list_int_IO : MonadO int IO := {
  print := output_byte stdout;
}.

Definition reactable (c1 c2 : int) : bool :=
  int_eqb (lxor c1 c2)
          (int_of_nat 32).

Definition react_f (stack : list int) (c : int) : list int :=
  match stack with
  | [] => [c]
  | c' :: stack' =>
    if reactable c c' then
      stack'
    else
      c :: stack
  end.

Definition react (cs : list int) : list int :=
  fold_left react_f cs [].

Section spec.

Ltac gd xs :=
  match xs with
  | (?xs, ?x) => generalize dependent x; gd xs
  | ?x => generalize dependent x
  end.

Section react_generic.

Context {A : Type}.

Class Reactive : Type :=
  can_react : A -> A -> Prop.
Context `{Reactive}.

Variant react_step : list A -> list A -> Prop :=
| RStep (cs1 : list A) (c1 c2 : A) (cs2 : list A) :
    can_react c1 c2 ->
    react_step (cs1 ++ c1 :: c2 :: cs2) (cs1 ++ cs2).

(* Reflexive transitive closure:
   [react_steps x z] holds when [x] can reach [z] after some
   number of [react_step]. *)
Definition react_steps := Rstar _ react_step.

Lemma react_cons_congr1 :
  forall c cs1 cs2,
    react_step cs1 cs2 -> react_step (c :: cs1) (c :: cs2).
Proof.
  intros ? ? ? [cs1 c1 c2 cs2].
  apply (RStep (c :: cs1)); auto.
Qed.

Lemma react_cons_congr :
  forall c cs1 cs2,
    react_steps cs1 cs2 ->
    react_steps (c :: cs1) (c :: cs2).
Proof.
  induction 1.
  - constructor.
  - econstructor; [|eauto]. apply react_cons_congr1; auto.
Qed.

Class GoodReactive : Prop := {
(* [can_react] should be an involutive function. *)
  can_react_symmetric :
    forall a b, can_react a b -> can_react b a;
  can_react_function :
    forall a b c, can_react a b -> can_react a c -> b = c;
}.

Context `{GoodReactive}.

Lemma can_react_cofunction :
  forall a b c, can_react a c -> can_react b c -> a = b.
Proof.
  intros; eapply can_react_function; eapply can_react_symmetric; eauto.
Qed.

(* We prove that [react_step] is [Confluent], i.e., the top and left
   sides of the following square imply the right and bottom ones.

     cs0 > ... > cs1
      v           v
     ...         ...
      v           v
     cs2 > ... > cs3
 *)

(* To prove that [react_step] is confluent: it is sufficient to
   show that it is *locally confluent* and *noetherian*. *)

(* [Locally_confluent]: the top and left sides of the square imply
   the right and bottom ones.

     x  >  y1
     v     v*
     y2 >* z
 *)
Lemma Locally_confluent_react_step : Locally_confluent _ react_step.
Proof.
  intros cs0 cs1 cs2 H01 H02.
  inversion H01; inversion H02; clear H01 H02.
  gd (cs0, cs1, cs2, cs5).
  induction cs3; simpl; intros.
  - destruct cs5 as [|c5' cs5]; simpl in *; subst.
    + exists cs1; inversion H5; subst; split; constructor.
    + destruct cs5; simpl in *; subst.
      * exists cs1; inversion H5; subst.
        apply can_react_symmetric in H1.
        eapply can_react_function in H1; eauto; subst.
        split; constructor.
      * exists (cs5 ++ cs6); inversion H5; subst.
        split; apply Rstar_contains_R.
        -- apply RStep; auto.
        -- apply (RStep []); auto.
  - destruct cs5; simpl in *.
    + destruct cs3; simpl in *; subst.
      * exists cs2; inversion H5; subst.
        eapply can_react_symmetric,
               (can_react_function _ a c2) in H4; eauto.
        subst; split; constructor.
      * exists (cs3 ++ cs4); inversion H5; subst.
        split; apply Rstar_contains_R.
        -- apply (RStep []); auto.
        -- apply RStep; auto.
    + specialize IHcs3 with (cs5 := cs5).
      subst; inversion H5; subst; clear H5.
      edestruct IHcs3 as [cs7 [Hcs7 Hcs7']]; eauto.
      exists (a :: cs7).
      split; apply react_cons_congr; auto.
Qed.

(* [Noetherian]: there is no infinite sequence of steps.
   In this case, the length decreases by two. *)
Lemma Noetherian_react_step : Noetherian _ react_step.
Proof.
  intros cs.
  (* Well-founded induction on [length cs]. *)
  remember (length cs) as n; generalize dependent cs;
    induction (lt_wf n) as [n Hn IH].
  constructor; intros cs1 Hcs1.
  eapply IH; eauto.
  destruct Hcs1; subst.
  repeat rewrite app_length.
  apply Nat.add_lt_mono_l. simpl; auto.
Qed.

Theorem Confluent_react_step : Confluent _ react_step.
Proof.
  apply Newman.
  - apply Noetherian_react_step.
  - apply Locally_confluent_react_step.
Qed.

(* As a corollary, fully reacting a polymer yields a unique result,
   showing that there is only one possible answer. *)

(* [cs] is inert if it can no longer react. *)
Definition inert (cs : list A) : Prop :=
  forall cs', ~ react_step cs cs'.

Definition fully_react (cs cs' : list A) : Prop :=
  react_steps cs cs' /\ inert cs'.

Corollary react_steps_injective :
  forall cs cs1 cs2,
    fully_react cs cs1 ->
    fully_react cs cs2 ->
    cs1 = cs2.
Proof.
  intros cs cs1 cs2 [Hcs1 Hinert1] [Hcs2 Hinert2].
  pose proof (Confluent_react_step cs cs1 cs2 Hcs1 Hcs2) as Hconfl.
  destruct Hconfl as [cs3 [Hcs13 Hcs23]].
  destruct Hcs13.
  - destruct Hcs23.
    + reflexivity.
    + exfalso; eapply Hinert2; eauto.
  - exfalso; eapply Hinert1; eauto.
Qed.

End react_generic.

Global Arguments Reactive : clear implicits.

End spec.

Section example.
Definition A := 0. Definition a := 1.
Definition B := 2. Definition b := 3.
Definition C := 4. Definition c := 5.
Instance Reactive_nat : Reactive nat :=
  fun (x y : nat) => S x = y \/ x = S y.
Fixpoint react_list (css : list (list nat)) : Prop :=
  match css with
  | cs :: (cs' :: _) as css =>
    react_step cs cs' /\
    react_list css
  | _ => True
  end.
Example react_ex :
  react_list
    [[A;c;C;a;C;B;A;c;C];
     [A;a;C;B;A;c;C];
     [C;B;A;c;C];
     [C;B;A]].
Proof.
  repeat constructor.
  - eapply (RStep [A]). right;auto.
  - eapply (RStep []). left;auto.
  - eapply (RStep [_; _; _]). right; auto.
Qed.
End example.
