From Coq Require Import
     List
     Relations Morphisms.
Import ListNotations.

From ITree Require Export
     ITree StdEffects MorphismsFacts.

From ExtLib Require Import
     Structures.Monad.
Import MonadNotation.
Local Open Scope monad_scope.

From advent.lib Require Import io rel.

(* We need [stateE] and [failureE] *)

Definition ioE (I O : Type) : Type -> Type := stateE (io_state I O).

Definition run_io {I O : Type} {E : Type -> Type}
           (s : io_state I O) :
  forall R, itree (ioE I O +' E) R -> itree E (io_state I O * R) :=
  fun _ => run_state s.

Instance MonadError_itree (E : Type -> Type)
         `{failureE -< E} : MonadError (itree E) := {
  error := fun _ s => fail s;
}.

Instance MonadI_itree (I O : Type) (E : Type -> Type)
         `{ioE I O -< E} : MonadI I (itree E) := {
  read :=
    s <- get;;
    match input s with
    | [] => ret None
    | c :: cs =>
      put (Mk_io_state cs (output s));;
      ret (Some c)
    end
}.

Instance MonadO_itree (I O : Type) (E : Type -> Type)
         `{ioE I O -< E} : MonadO O (itree E) := {
  print x :=
    s <- get;;
    put (Mk_io_state (input s) (output s ++ [x]));
}.

Instance FoldRead_itree (I O : Type) (E : Type -> Type)
         `{ioE I O -< E} : FoldRead I (itree E) := {
  fold_read S f s0 :=
    mfix (fun _ => S) (fun _ inc loop s =>
      oi <- inc _ read;;
      match oi with
      | None => ret s
      | Some i => loop (f s i)
      end
    ) s0;
}.

(* We could generalize [failureE], but we may need to be careful
   about how instances resolve. *)
(* Compared to [io_rel], we get determinism for free. *)
Definition itree_spec' {I O R : Type}
           (t : itree (ioE I O +' failureE) R)
           (s s' : io_state I O) (r : R) : Prop :=
  eutt (run_io s _ t)
       (Ret (s', r)).

Definition itree_spec {I O : Type}
           (t : itree (ioE I O +' failureE) unit)
           (i : list I) (o : list O) :=
  exists s',
    itree_spec' t (Mk_io_state i []) s' tt /\
    output s' = o.

Instance Proper_run_io {I O R : Type} {E : Type -> Type} s :
  Proper (eutt ==> eutt)
         (@run_io I O E s R).
Proof.
Admitted.

Instance Proper_itree_spec' {I O R : Type} :
  Proper (eutt ==> eq ==> eq ==> eq ==> iff)
         (@itree_spec' I O R).
Proof.
  intros t1 t2 Ht i1 i2 [] o1 o2 [] r1 r2 [].
  unfold itree_spec'. rewrite Ht; reflexivity.
Qed.

Lemma spec_bind {I O A B : Type}
      (a : A)
      (s1 s2 s3 : io_state I O)
      (m : itree _ A) (k : A -> itree _ B)
      (b : B) :
  itree_spec' m s1 s2 a ->
  itree_spec' (k a) s2 s3 b ->
  itree_spec' (m >>= k) s1 s3 b.
Proof.
  unfold itree_spec', run_io, run_state.
  intros Hm Hk.
  rewrite interp_state_bind.
  subst.
  rewrite Hm.
  rewrite ret_bind.
  simpl.
  rewrite Hk.
  reflexivity.
Qed.

Lemma spec_fold_read {I O A : Type}
      (f : A -> I -> A)
      (s1 s2 : io_state I O) (a0 : A) :
  s2 = Mk_io_state [] (output s1) ->
  itree_spec' (fold_read f a0) s1 s2 (fold_left f (input s1) a0).
Proof.
  pose proof @spec_bind as spec_bind. simpl in spec_bind.
  remember (input s1) as i1.
  revert a0 s2. generalize dependent s1.
  induction i1; intros.
  - unfold fold_read, FoldRead_itree.
    rewrite mfix_unfold.
    eapply spec_bind.
    + eapply spec_bind.
      * unfold itree_spec', run_io, run_state.
        unfold get, lift, embed, Embeddable_itree, lift.
        rewrite interp_state_liftE.
        simpl. reflexivity.
      * rewrite <- Heqi1.
        unfold itree_spec', run_io, run_state. simpl.
        rewrite interp_state_ret. reflexivity.
    + simpl.
      unfold itree_spec', run_io, run_state.
      rewrite interp_state_ret.
      destruct s1.
      simpl in Heqi1. subst. reflexivity.
  - unfold fold_read, FoldRead_itree.
    rewrite mfix_unfold.
    eapply spec_bind. simpl. unfold id.
    eapply spec_bind.
    unfold itree_spec', run_io, run_state.
    unfold get, lift, embed, Embeddable_itree, lift.
    rewrite interp_state_liftE.
    simpl. reflexivity.
    rewrite <- Heqi1.
    eapply spec_bind.
    unfold itree_spec', run_io, run_state.
    unfold put, lift.
    repeat (unfold embed, Embeddable_forall, Embeddable_itree, lift).
    rewrite interp_state_liftE.
    simpl. reflexivity.
    unfold itree_spec', run_io, run_state.
    rewrite interp_state_ret.
    reflexivity.
    simpl.
    apply IHi1; auto.
Qed.
