From Coq Require Import
     List ZArith Ascii String
     extraction.ExtrOcamlIntConv.
Import ListNotations.

From SimpleIO Require SimpleIO.

From ExtLib Require Import
     Structures.Monads.
Import MonadNotation.
Local Open Scope monad.

From advent Require Import lib.

Section main.

Context {m : Type -> Type} `{Monad m}
        `{MonadI Z m} `{MonadO Z m} `{MonadFix m}.

(* Read integers and accumulate their sum. *)
Definition main : m unit :=
  fold_read (fun z0 z => z0 + z)%Z 0%Z >>= print.

End main.

Import SimpleIO.

Definition exec : io_unit := IO.unsafe_run main.

Extraction "day01_1.ml" exec.


Section spec.

(* Sum of a list of numbers. *)
Fixpoint sum_Z (zs : list Z) : Z :=
  match zs with
  | [] => 0
  | z :: zs => z + sum_Z zs
  end.

Lemma sum_Z_fold (zs : list Z) :
  sum_Z zs = fold_left Z.add zs 0%Z.
Proof.
  assert
    (H : forall zs z0, fold_left Z.add zs z0 = (z0 + sum_Z zs)%Z).
  - clear. induction zs; intro z; simpl.
    + rewrite Z.add_0_r. auto.
    + rewrite Z.add_assoc. auto.
  - rewrite H; auto.
Qed.

(* If you run [main] with the input [zs], then the printed output
   will be exactly [sum_Z zs]. *)
Definition correct (main : io_rel Z Z unit) : Prop :=
  forall zs, rel_spec Z Z main zs [sum_Z zs].

Theorem correct_main : correct main.
Proof.
  intros zs.
  unfold rel_spec.
  exists (Mk_io_state [] [sum_Z zs]); split; [| auto].
  exists (sum_Z zs); eexists.
  split.
  - apply fold_read_rel.
    split; [| reflexivity].
    apply sum_Z_fold.
  - simpl; auto.
Qed.

End spec.
