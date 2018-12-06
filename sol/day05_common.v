Set Warnings "-extraction-opaque-accessed".

From Coq Require Import
     Ascii String List Arith
     OrderedTypeEx FMapAVL
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

Context {A : Type}.
Context (can_react : A -> A -> Prop).

Variant react_step : list A -> list A -> Prop :=
| RStep (c1 c2 : A) (cs1 cs2 : list A) :
    can_react c1 c2 ->
    react_step (cs1 ++ c1 :: c2 :: cs2) (cs1 ++ cs2).

(* Reflexive transitive closure of [react_step]. *)
Inductive react_steps : list A -> list A -> Prop :=
| Steps0 (cs : list A) : react_steps cs cs
| Steps1 (cs cs' cs'' : list A) :
    react_step  cs  cs'  ->
    react_steps cs' cs'' ->
    react_steps cs  cs''
.

(* [can_react] should be an involutive function. *)
Hypothesis can_react_symmetric :
  forall a b, can_react a b -> can_react b a.
Hypothesis can_react_function :
  forall a b c, can_react a b -> can_react a c -> b = c.

Lemma can_react_cofunction :
  forall a b c, can_react a c -> can_react b c -> a = b.
Proof.
  intros; eapply can_react_function, can_react_symmetric; eauto.
Qed.

Ltac gd xs :=
  match xs with
  | (?xs, ?x) => generalize dependent x; gd xs
  | ?x => generalize dependent x
  end.

(* The top and left sides of the square imply the right and bottom
   ones.

     cs0 > cs1
      v     v
     cs2 > cs3

 *)
Lemma react_step_confluent :
  forall cs0 cs1 cs2,
    react_step cs0 cs1 -> react_step cs0 cs2 ->
    cs1 = cs2 \/ (exists cs3,
                     react_step cs1 cs3 /\ react_step cs2 cs3).
Proof.
  intros cs0 cs1 cs2 H01 H02.
  inversion H01; inversion H02; clear H01 H02.
  gd (cs1, cs2, c1, c2, cs4, c0, c3, cs5, cs6).
  induction cs3; simpl; intros.
  - destruct cs5 as [|c5' cs5]; simpl in *.
    + left; subst. inversion H3; subst; auto.
    + destruct cs5; simpl in *.
      * left; subst. inversion H3; subst. f_equal.
        eapply can_react_function; eauto.
      * right; subst. inversion H3; subst.
        exists (cs5 ++ cs6).
        split.
        { apply RStep; auto. }
        { apply (RStep _ _ []); auto. }
  - admit.
Abort.

End spec.

Section example.
Definition A := 0. Definition a := 1.
Definition B := 2. Definition b := 3.
Definition C := 4. Definition c := 5.
Definition can_react_nat (x y : nat) : Prop := S x = y \/ x = S y.
Fixpoint react_list (css : list (list nat)) : Prop :=
  match css with
  | cs :: (cs' :: _) as css =>
    react_step can_react_nat cs cs' /\
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
  - eapply (RStep _ c C [A]). right;auto.
  - eapply (RStep _ A a []). left;auto.
  - eapply (RStep _ c C [_; _; _]). right; auto.
Qed.
End example.
