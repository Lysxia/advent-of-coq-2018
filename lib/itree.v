From Coq Require Import
     List.
Import ListNotations.

From ITree Require Export
     ITree OpenSum Eq.UpToTaus Fix.

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
