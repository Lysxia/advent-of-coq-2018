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
  mfix (fun loop z0 =>
    oz <- read;;
    match oz with
    | None => print z0
    | Some z => loop (z + z0)%Z
    end) 0%Z.

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

(* If you run [main] with the input [zs], then the printed output
   will be exactly [sum_Z zs]. *)
Definition correct (main : io_rel Z Z unit) : Prop :=
  forall zs, rel_spec Z Z main zs [sum_Z zs].

Theorem correct_main : correct main.
Proof.
  intros zs.
  unfold rel_spec.
  exists (Mk_io_state [] [sum_Z zs]); split; [| auto].
  unfold rel_spec, main; simpl.
  match goal with
  | [ |- lfp_rel1 ?body _ _ _ _ ] =>
    assert (H : forall z0 zs,
               lfp_rel1 body z0 (initial zs)
                       (Mk_io_state [] [(z0 + sum_Z zs)%Z]) tt)
  end.
  { clear zs.
    intros z0 zs.
    revert z0; induction zs as [|z zs IH]; intros z0; apply lfp_rel_fold.
    - exists None, (initial []).
      repeat (split; auto).
      simpl. repeat f_equal.
      apply Z.add_0_r.
    - exists (Some z), (initial zs).
      repeat (split; auto).
      + left. exists z; auto.
      + simpl.
        replace (z0 + (z + sum_Z zs))%Z with ((z + z0) + sum_Z zs)%Z.
        apply IH.
        rewrite Z.add_assoc.
        rewrite (Z.add_comm z).
        reflexivity.
  }
  apply H.
Qed.

End spec.
