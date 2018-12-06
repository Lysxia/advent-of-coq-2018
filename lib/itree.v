From Coq Require Import
     List
     Relations Morphisms.
Import ListNotations.

From ITree Require Export
     ITree OpenSum Eq.Eq Eq.UpToTaus Fix MorphismsFacts.

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
           (i : list I) (o : list O) (r : R) : Prop :=
  forall i' o',
    eutt (run_io (Mk_io_state (i ++ i') o') _ t)
         (Ret (Mk_io_state i' (o' ++ o), r)).

Definition itree_spec {I O : Type}
           (t : itree (ioE I O +' failureE) unit)
           (i : list I) (o : list O) :=
  itree_spec' t i o tt.

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
  split; intros H i o; [rewrite <- Ht | rewrite Ht]; auto.
Qed.

Lemma spec_bind {I O A B : Type}
      (a : A)
      (ia ib : list I)
      (oa ob : list O)
      (m : itree _ A) (k : A -> itree _ B)
      (i : list I) (o : list O) (b : B) :
  itree_spec' m ia oa a ->
  itree_spec' (k a) ib ob b ->
  i = ia ++ ib ->
  o = oa ++ ob ->
  itree_spec' (m >>= k) i o b.
Proof.
  intros Hm Hk Hi Ho i' o'.
  unfold itree_spec', run_io, run_state in *.
  rewrite interp_state_bind.
  subst. rewrite <- app_assoc.
  rewrite Hm.
  rewrite ret_bind.
  simpl.
  rewrite Hk.
  rewrite <- app_assoc.
  reflexivity.
Qed.
