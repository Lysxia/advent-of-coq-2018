(* Define IO as a relation between input and output states. *)

From Coq Require Import
     List ZArith String
     extraction.ExtrOcamlIntConv.
Import ListNotations.

From Coq.extraction Require Import
     ExtrOcamlIntConv.

From ExtLib Require Import
     Data.Monads.OptionMonad
     Structures.Monads.

From SimpleIO Require Import
     IOMonad CoqPervasives Utils.

From advent.lib Require Import
     io.

(* State [s -> (s * a)] as a relation. *)
Definition state_rel (S : Type) (A : Type) : Type :=
  S -> S -> A -> Prop.

Record io_state (I O : Type) := Mk_io_state {
  input : list I;
  output : list O;
}.

Arguments Mk_io_state {I O} _ _.
Arguments input {I O} _.
Arguments output {I O} _.

Definition initial {I O : Type} (i : list I) : io_state I O :=
  Mk_io_state i [].

Definition drop_input {I O : Type} (r : io_state I O) : io_state I O :=
  let '(Mk_io_state i o) := r in
  Mk_io_state (tl i) o.

Definition push_output {I O : Type}
           (z : O) (r : io_state I O) : io_state I O :=
  let '(Mk_io_state i o) := r in
  Mk_io_state i (o ++ [z]).

Definition io_rel (I O : Type) : Type -> Type :=
  state_rel (io_state I O).

Definition rel_spec (I O : Type) :
  io_rel I O unit -> list I -> list O -> Prop :=
  fun x i o =>
    exists s,
      x (initial i) s tt /\
      output s = o.

Instance Monad_state_rel (S : Type) : Monad (state_rel S) := {
  ret _ x := fun s1 s2 x' => s2 = s1 /\ x' = x;
  bind _ _ m k := fun s1 s3 y =>
    exists x s2, m s1 s2 x /\ k x s2 s3 y
}.

Instance MonadError_state_rel (S : Type) : MonadError (state_rel S) := {
  error _ _ := fun _ _ _ => False
}.

Instance MonadI_io_rel (I O : Type) : MonadI I (io_rel I O) := {
  read := fun s1 s2 x' =>
    (exists z,
      input s1 = z :: input s2 /\
      s2 = drop_input s1 /\
      x' = Some z) \/
    (s2 = s1 /\ x' = None);
}.

Instance MonadO_io_rel (I O : Type) : MonadO O (io_rel I O) := {
  print z := fun s1 s2 x' =>
    s2 = push_output z s1 /\
    x' = tt
}.

Definition incl_rel {S A : Type} (r1 r2 : state_rel S A) :=
  forall s1 s2 a, r1 s1 s2 a -> r2 s1 s2 a.

Definition incl_rel_1 {S A B : Type}
           (r1 r2 : A -> state_rel S B) :=
  forall x, incl_rel (r1 x) (r2 x).

Lemma incl_rel_1_refl {S A B : Type} (r : A -> state_rel S B) :
  incl_rel_1 r r.
Proof.
  intros x z1 z2 y; auto.
Qed.

Inductive lfp_rel {S A B : Type}
          (gf : (A -> state_rel S B) -> (A -> state_rel S B))
          (a : A) (s1 s2 : S) (b : B) : Prop :=
| LFP
    (P : A -> state_rel S B)
    (P_ind : incl_rel_1 P (lfp_rel gf))
    (P_holds : gf P a s1 s2 b).

Definition monotonic_rel {S A B : Type}
           (gf : (A -> state_rel S B) -> (A -> state_rel S B)) :=
  forall r1 r2,
    incl_rel_1 r1 r2 ->
    incl_rel_1 (gf r1) (gf r2).

Lemma lfp_rel_unfold {S A B : Type}
      (gf : (A -> state_rel S B) -> (A -> state_rel S B))
      (mon_gf : monotonic_rel gf) :
  incl_rel_1 (lfp_rel gf) (gf (lfp_rel gf)).
Proof.
  intros x z1 z2 y [P P_ind P_holds].
  eapply mon_gf.
  apply P_ind.
  apply P_holds.
Qed.

Lemma lfp_rel_fold {S A B : Type}
      (gf : (A -> state_rel S B) -> (A -> state_rel S B)) :
  incl_rel_1 (gf (lfp_rel gf)) (lfp_rel gf).
Proof.
  intros x z1 z2 y Hgf.
  apply LFP with (P := lfp_rel gf).
  apply incl_rel_1_refl.
  auto.
Qed.

Lemma really_lfp {S A B : Type}
      (gf : (A -> state_rel S B) -> (A -> state_rel S B))
      (mon_gf : monotonic_rel gf)
      (fp : A -> state_rel S B)
      (H_fp : incl_rel_1 (gf fp) fp) :
  incl_rel_1 (lfp_rel gf) fp.
Proof.
  intros x z1 z2 y.
  induction 1 as [x z1 z2 y P P_ind IH P_holds].
  apply H_fp.
  apply mon_gf with (r1 := P); auto.
Qed.

Instance MonadFix_state_rel (S : Type) : MonadFix (state_rel S) := {
  mfix _ _ := lfp_rel
}.
