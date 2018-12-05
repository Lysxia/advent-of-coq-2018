(* Here we model IO as a partial function between input and output
   states: [IO a ~ (io_state -> io_state * a)], actually
   implemented as [io_state -> io_state -> a -> Prop].

   Partiality is caused by the presence of a general (monadic)
   fixpoint combinator ([mfix]).
 *)

From Coq Require Import
     List ZArith String
     RelationClasses
     extraction.ExtrOcamlIntConv.
Import ListNotations.

From Coq.extraction Require Import
     ExtrOcamlIntConv.

From ExtLib Require Import
     Data.Monads.OptionMonad
     Structures.Monads.

From advent.lib Require Import
     io utils.

(* First, some general definitions about state [S -> (S * A)].
   We then specialize [S] to a simple model of IO state. *)

(* [state_rel]: state [S -> (S * A)] as a relation. *)
Definition state_rel (S : Type) (A : Type) : Type :=
  S -> S -> A -> Prop.

(* [state_rel] is a monad. *)
Instance Monad_state_rel (S : Type) : Monad (state_rel S) := {
  ret _ x := fun s1 s2 x' => s2 = s1 /\ x' = x;
  bind _ _ m k := fun s1 s3 y =>
    exists x s2, m s1 s2 x /\ k x s2 s3 y
}.

(* Errors are modelled by the empty relation. *)
Instance MonadError_state_rel (S : Type) : MonadError (state_rel S) := {
  error _ _ := fun _ _ _ => False
}.

(* Relations are preordered by implication. *)
Definition incl_rel {S A : Type} (r1 r2 : state_rel S A) :=
  forall s1 s2 a, r1 s1 s2 a -> r2 s1 s2 a.

(* Logical equivalence. *)
Definition eq_rel {S A : Type} (r1 r2 : state_rel S A) :=
  incl_rel r1 r2 /\ incl_rel r2 r1.

Instance Transitive_incl_rel {S A} : Transitive (@incl_rel S A).
Proof. firstorder. Qed.

Instance Transitive_eq_rel {S A} : Transitive (@eq_rel S A).
Proof. firstorder. Qed.

(* For [mfix], we will be manipulating relations with an extra
   parameter: [A -> S -> S -> B -> Prop]. *)
Definition incl_rel1 {S A B : Type}
           (r1 r2 : A -> state_rel S B) :=
  forall x, incl_rel (r1 x) (r2 x).

(* Reflexivity of [incl_rel1]. *)
Lemma incl_rel1_refl {S A B : Type} (r : A -> state_rel S B) :
  incl_rel1 r r.
Proof.
  intros x z1 z2 y; auto.
Qed.

(* Least fixed point of the "relation transformer", [gf] (or
   "generating function"; note how it maps relations to relations).
   [gf] is assumed to be monotonic (see below).
   Definition inspired by [paco] (https://github.com/snu-sf/paco). *)
Inductive lfp_rel1 {S A B : Type}
          (gf : (A -> state_rel S B) -> (A -> state_rel S B))
          (a : A) (s1 s2 : S) (b : B) : Prop :=
| LFP
    (P : A -> state_rel S B)
    (P_ind : incl_rel1 P (lfp_rel1 gf))
    (P_holds : gf P a s1 s2 b).

(* [monotonic_rel1 gf : Prop] : the relation transformer [gf]
   is monotonic. *)
Definition monotonic_rel1 {S U V A B : Type}
           (gf : (U -> state_rel S V) -> (A -> state_rel S B)) :=
  forall r1 r2,
    incl_rel1 r1 r2 ->
    incl_rel1 (gf r1) (gf r2).

(* [lfp_rel1 gf] is included in [gf (lfp_rel1 gf)]... *)
Lemma lfp_rel_unfold {S A B : Type}
      (gf : (A -> state_rel S B) -> (A -> state_rel S B))
      (mon_gf : monotonic_rel1 gf) :
  incl_rel1 (lfp_rel1 gf) (gf (lfp_rel1 gf)).
Proof.
  intros x z1 z2 y [P P_ind P_holds].
  eapply mon_gf.
  apply P_ind.
  apply P_holds.
Qed.

(* ... and conversely. Therefore, [lfp_rel1] does define a fixed
   point... *)
Lemma lfp_rel_fold {S A B : Type}
      (gf : (A -> state_rel S B) -> (A -> state_rel S B)) :
  incl_rel1 (gf (lfp_rel1 gf)) (lfp_rel1 gf).
Proof.
  intros x z1 z2 y Hgf.
  apply LFP with (P := lfp_rel1 gf).
  apply incl_rel1_refl.
  auto.
Qed.

(* ... and it is in fact the smallest: every other fixed point [fp]
   contains [lfp_rel1 gf]. *)
Lemma really_lfp {S A B : Type}
      (gf : (A -> state_rel S B) -> (A -> state_rel S B))
      (mon_gf : monotonic_rel1 gf)
      (fp : A -> state_rel S B)
      (H_fp : incl_rel1 (gf fp) fp) :
  incl_rel1 (lfp_rel1 gf) fp.
Proof.
  intros x z1 z2 y.
  induction 1 as [x z1 z2 y P P_ind IH P_holds].
  apply H_fp.
  apply mon_gf with (r1 := P); auto.
Qed.

(* Fixed-point semantics for [mfix]. *)
Instance MonadFix_state_rel (S : Type) : MonadFix (state_rel S) := {
  mfix _ _ := lfp_rel1
}.

(* Utilities to prove monotonicity. *)

Lemma monotonic_refl (S U V W A : Type)
      (m : state_rel S A) :
  monotonic_rel1 (fun (_ : U -> _ V) (_ : W) => m).
Proof.
  unfold monotonic_rel1, incl_rel1, incl_rel; auto.
Qed.

Lemma monotonic_id (S U V W : Type)
      (g : W -> U) :
  monotonic_rel1 (fun (f : U -> state_rel S V) (w : W) => f (g w)).
Proof.
  unfold monotonic_rel1, incl_rel1; auto.
Qed.

Lemma monotonic_ret (S U V W A : Type)
      (g : W -> A) :
  monotonic_rel1 (fun (f : U -> state_rel S V) (w : W) => ret (g w)).
Proof.
  unfold monotonic_rel1, incl_rel1, incl_rel; auto.
Qed.

Lemma monotonic_bind (S U V W A B : Type)
      (m : (U -> state_rel S V) -> W -> state_rel S A)
      (k : (U -> state_rel S V) -> W -> A -> state_rel S B)
      (mon_m : monotonic_rel1 m)
      (mon_k : forall a, monotonic_rel1 (fun f w => k f w a)) :
  monotonic_rel1 (fun f w => pbind (m f w) (k f w)).
Proof.
  intros r1 r2 Hr12 w s1 s3 b [a [s2 [Hm Hk]]].
  exists a, s2.
  firstorder.
  specialize (mon_k a).
  unfold monotonic_rel1 in mon_k.
  eapply mon_k; eauto.
Qed.

(* Modelling [IO]. *)

(* We represent IO state as a sequence of inputs and a sequence
   of outputs. For problems like AoC that should be quite enough.
   The input and output types are parameters: we trust the
   parsing/printing done by [read]/[print], there is still quite
   some space left to play with verification.
 *)
Record io_state (I O : Type) := Mk_io_state {
  input : list I;
  output : list O;
}.

Arguments Mk_io_state {I O} _ _.
Arguments input {I O} _.
Arguments output {I O} _.

(* Construct an initial state from an initial input sequence. *)
Definition initial {I O : Type} (i : list I) : io_state I O :=
  Mk_io_state i [].

(* Update the state on a [read]. *)
Definition drop_input {I O : Type} (r : io_state I O) : io_state I O :=
  let '(Mk_io_state i o) := r in
  Mk_io_state (tl i) o.

(* Update the state on a [print]. *)
Definition push_output {I O : Type}
           (z : O) (r : io_state I O) : io_state I O :=
  let '(Mk_io_state i o) := r in
  Mk_io_state i (o ++ [z]).

(* [state_rel] specialized with [io_state]. *)
Definition io_rel (I O : Type) : Type -> Type :=
  state_rel (io_state I O).

(* Toplevel specification, we model an [IO unit] program
   as a relation between inputs and outputs. *)
Definition rel_spec (I O : Type) :
  io_rel I O unit -> list I -> list O -> Prop :=
  fun x i o =>
    exists s,
      x (initial i) s tt /\
      output s = o.

(* Model [read] in [io_rel]. *)
Instance MonadI_io_rel (I O : Type) : MonadI I (io_rel I O) := {
  read := fun s1 s2 x' =>
    (exists z,
      input s1 = z :: input s2 /\
      s2 = drop_input s1 /\
      x' = Some z) \/
    (input s1 = [] /\ s2 = s1 /\ x' = None);
}.

(* Model [print] in [io_rel]. *)
Instance MonadO_io_rel (I O : Type) : MonadO O (io_rel I O) := {
  print z := fun s1 s2 x' =>
    s2 = push_output z s1 /\
    x' = tt
}.

(* Specification of [fold_read]. *)
Lemma fold_read_rel {I O A : Type} (f : A -> I -> A) (a0 : A) :
  eq_rel (fold_read f a0)
         (fun (s1 s2 : io_state I O) (a1 : A) =>
            a1 = fold_left f (input s1) a0 /\
            s2 = Mk_io_state [] (output s1)).
Proof.
  split.
  - intros s1 s2 xs.
    unfold fold_read.
    match goal with
    | [ |- mfix ?body _ _ _ _ -> _ ] =>
      assert (mon_body : monotonic_rel1 body)
    end.
    { apply monotonic_bind.
      - apply monotonic_refl.
      - intros [i|].
        { apply monotonic_id. }
        { apply monotonic_ret. }
    }
    match goal with
    | [ |- mfix ?body _ _ _ _ -> _ ] =>
      assert (H : forall acc s1 s2 a1,
                 lfp_rel1 body acc s1 s2 a1 ->
                 a1 = fold_left f (input s1) acc /\
                 s2 = Mk_io_state [] (output s1)); [|auto]
    end.
    { revert mon_body; clear; intros mon_body acc [is1 os1].
      revert acc. induction is1 as [| i1 is1]; intros acc s2 xs Hloop.
      - apply lfp_rel_unfold in Hloop; auto.
        destruct Hloop as [ox [s1' [Hread Hloop]]].
        destruct Hread as [[i1 [Hi1]] | [Hi [Hs1' Hox]]].
        + discriminate Hi1.
        + subst ox.
          destruct Hloop; subst; auto.
      - apply lfp_rel_unfold in Hloop; auto.
        destruct Hloop as [ox [s1' [Hread Hloop]]].
        destruct Hread as [[i1' [Hi1 [Hs1' Hox]]] | [Hs1' Hox]].
        + subst ox s1'.
          simpl in Hi1; inversion Hi1; subst.
          apply IHis1 in Hloop.
          destruct Hloop as [Hxs Hs2]. subst.
          auto.
        + discriminate.
    }
  - intros s1 s2 a1 [Ha1 Hs2].
    unfold fold_read.
    match goal with
    | [ |- mfix ?body _ _ _ _ ] =>
      assert (H : forall acc s1 s2 a1,
                 a1 = fold_left f (input s1) acc ->
                 s2 = Mk_io_state [] (output s1) ->
                 lfp_rel1 body acc s1 s2 a1); [| apply H; auto]
    end.
    { clear.
      intros acc s1. revert acc.
      remember (input s1) as is1 eqn:Hs1.
      generalize dependent s1.
      induction is1 as [|i1 is1 IH];
        intros s1 Hs1 acc s2 xs His1 Hs2;
        apply lfp_rel_fold.
      + exists None, s2.
        split.
        * right; destruct s1, s2; simpl in *; subst; auto.
        * simpl; auto.
      + exists (Some i1), (Mk_io_state is1 (output s1)).
        split.
        * left. exists i1. simpl.
          destruct s1; simpl in *; subst; auto.
        * apply IH; auto.
    }
Qed.

(* Specification of [read_all]: it consumes all the input and
   returns it in a list. *)
Lemma read_all_rel {I O : Type} :
  eq_rel read_all
         (fun (s1 s2 : io_state I O) xs =>
            xs = input s1 /\
            s2 = Mk_io_state [] (output s1)).
Proof.
  split; intros s1 s2 a1.
  - intros [is1' [s1' [H1' [? ?]]]]; subst.
    apply fold_read_rel in H1'.
    rewrite fold_left_cons in H1'.
    destruct H1'; subst.
    unfold rev'; rewrite <- rev_alt, rev_involutive.
    auto.
  - intros [? ?]; subst.
    exists (rev (input s1)). eexists.
    split.
    + apply fold_read_rel.
      split.
      * rewrite fold_left_cons; auto.
      * reflexivity.
    + unfold rev'; rewrite <- rev_alt, rev_involutive.
      simpl; auto.
Qed.
