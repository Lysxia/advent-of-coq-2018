(* Mocking the IO interface with pure functions. *)

From Coq Require Import
     List ZArith
     extraction.ExtrOcamlIntConv.
Import ListNotations.

From Coq.extraction Require Import
     ExtrOcamlIntConv.

From ExtLib Require Import
     Data.Monads.OptionMonad
     Structures.Monads.

From advent.lib Require Import
     io.

Definition input : Type := list Z.
Definition output : Type := list Z.

Record mock (r : Type) (a : Type) : Type := Mk_mock {
  un_mock :
    (a -> output -> input (* remaining *) -> r) ->
    input ->
    r;
}.

Arguments Mk_mock {r a} _.
Arguments un_mock {r a} _.

Global Instance Monad_mock r : Monad (mock r) := {
  ret _ a := Mk_mock (fun k => k a []);
  bind _ _ m k := Mk_mock (fun q =>
    un_mock m (fun a o =>
    un_mock (k a) (fun a o' =>
    q a (o ++ o'))));
}.

Global Instance MonadIOZ_mock r : MonadIOZ (mock r) := {
  read_Z := Mk_mock (fun k zs =>
    match zs with
    | [] => k None [] []
    | z :: zs => k (Some z) [] zs
    end);
  print_Z z := Mk_mock (fun k zs => k tt [] [z]);
}.

(* Fuel for [mfix] *)
Definition fuelT (m : Type -> Type) a :=
  nat -> m (option a).

Import MonadNotation.
Local Open Scope monad_scope.

Instance Monad_fuelT (m : Type -> Type)
         `{Monad m} : Monad (fuelT m) := {
  ret _ a := fun _ => Monad.ret (Some a);
  bind _ _ m k := fun fuel =>
    o <- m fuel;;
    match o with
    | None => Monad.ret None
    | Some a => k a fuel
    end;
}.

Instance MonadFix_fuelT (m : Type -> Type)
         `{Monad m} : MonadFix (fuelT m) := {
  mfix _ _ gf := fun a fuel0 =>
    (fix go fuel a :=
      match fuel with
      | O => Monad.ret None
      | S fuel' => gf (fun a _ => go fuel' a) a fuel0
      end) fuel0 a
}.

Instance MonadIOZ_fuelT (m : Type -> Type)
         `{Monad m} `{MonadIOZ m} : MonadIOZ (fuelT m) := {
  read_Z := fun _ => liftM Some read_Z;
  print_Z z := fun _ => liftM Some (print_Z z);
}.
