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

Record io_state := Mk_io_state {
  input : list Z;
  output : list Z;
}.

Definition initial (i : list Z) : io_state := Mk_io_state i [].

Definition drop_input (r : io_state) : io_state :=
  let '(Mk_io_state i o) := r in
  Mk_io_state (tl i) o.

Definition push_output (z : Z) (r : io_state) : io_state :=
  let '(Mk_io_state i o) := r in
  Mk_io_state i (o ++ [z]).

(* State [s -> (s * a)] as a relation. *)
Definition state_rel (s : Type) (a : Type) : Type :=
  s -> s -> a -> Prop.

Definition io_rel : Type -> Type := state_rel io_state.

Definition rel_spec : io_rel unit -> io_state -> io_state -> Prop :=
  fun x i o => x i o tt.

Instance Monad_state_rel s : Monad (state_rel s) := {
  ret _ x := fun s1 s2 x' => s2 = s1 /\ x' = x;
  bind _ _ m k := fun s1 s3 y =>
    exists x s2, m s1 s2 x /\ k x s2 s3 y
}.

Instance MonadError_state_rel s : MonadError (state_rel s) := {
  error _ _ := fun _ _ _ => False
}.

Instance MonadIZ_io_rel : MonadI Z io_rel := {
  read := fun s1 s2 x' =>
    (exists z,
      input s1 = z :: input s2 /\
      s2 = drop_input s1 /\
      x' = Some z) \/
    (s2 = s1 /\ x' = None);
}.

Instance MonadOZ_io_rel : MonadO Z io_rel := {
  print z := fun s1 s2 x' =>
    s2 = push_output z s1 /\
    x' = tt
}.

Definition incl_rel_1 {a b s : Type}
           (r1 r2 : a -> state_rel s b) :=
  forall x z1 z2 y,
    r1 x z1 z2 y -> r2 x z1 z2 y.

Lemma incl_rel_1_refl {a b s : Type} (r : a -> state_rel s b) :
  incl_rel_1 r r.
Proof.
  intros x z1 z2 y; auto.
Qed.

Inductive lfp_rel {a b : Type} {s : Type}
          (gf : (a -> state_rel s b) -> (a -> state_rel s b))
          (x : a)
          (z1 : s)
          (z2 : s)
          (y : b) : Prop :=
| LFP
    (P : a -> state_rel s b)
    (P_ind : incl_rel_1 P (lfp_rel gf))
    (P_holds : gf P x z1 z2 y).

Definition monotonic_rel {a b : Type} {s : Type}
           (gf : (a -> state_rel s b) -> (a -> state_rel s b)) :=
  forall r1 r2,
    incl_rel_1 r1 r2 ->
    incl_rel_1 (gf r1) (gf r2).

Lemma lfp_rel_unfold {a b : Type} {s : Type}
      (gf : (a -> state_rel s b) -> (a -> state_rel s b))
      (mon_gf : monotonic_rel gf) :
  incl_rel_1 (lfp_rel gf) (gf (lfp_rel gf)).
Proof.
  intros x z1 z2 y [P P_ind P_holds].
  eapply mon_gf.
  apply P_ind.
  apply P_holds.
Qed.

Lemma lfp_rel_fold {a b s : Type}
      (gf : (a -> state_rel s b) -> (a -> state_rel s b)) :
  incl_rel_1 (gf (lfp_rel gf)) (lfp_rel gf).
Proof.
  intros x z1 z2 y Hgf.
  apply LFP with (P := lfp_rel gf).
  apply incl_rel_1_refl.
  auto.
Qed.

Lemma really_lfp {a b s : Type}
      (gf : (a -> state_rel s b) -> (a -> state_rel s b))
      (mon_gf : monotonic_rel gf)
      (fp : a -> state_rel s b)
      (H_fp : incl_rel_1 (gf fp) fp) :
  incl_rel_1 (lfp_rel gf) fp.
Proof.
  intros x z1 z2 y.
  induction 1 as [x z1 z2 y P P_ind IH P_holds].
  apply H_fp.
  apply mon_gf with (r1 := P); auto.
Qed.

Instance MonadFix_state_rel s : MonadFix (state_rel s) := {
  mfix _ _ := lfp_rel
}.
