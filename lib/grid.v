(* A simple library for representing and displaying points on a
   grid. *)

From Coq Require Import
     List ZArith FMapAVL OrderedTypeEx.
Import ListNotations.

Module ZMap := FMapAVL.Make Z_as_OT.

(* First index by [y] then [x]. So it can be more efficiently
   displayed line by line. *)
Variant Grid (A : Type) : Type :=
| MkGrid : ZMap.t (ZMap.t A) -> Grid A
.

Arguments MkGrid {A}.

Definition empty_grid (A : Type) : Grid A :=
  MkGrid (ZMap.empty _).

Module GridZ.

Definition index {A : Type} (g : Grid A) (y x : Z) : option A :=
  let '(MkGrid g) := g in
  match ZMap.find y g with
  | None => None
  | Some gy => ZMap.find x gy
  end.

(* Index with a default value. *)
Definition index' {A : Type} (a : A) (g : Grid A) (y x : Z) : A :=
  match index g y x with
  | None => a
  | Some a' => a'
  end.

Definition insert {A : Type} (y x : Z) (a : A) (g : Grid A) : Grid A :=
  let '(MkGrid g) := g in
  let gy :=
      match ZMap.find y g with
      | None => ZMap.empty _
      | Some gy => gy
      end in
  MkGrid (ZMap.add y (ZMap.add x a gy) g).

Definition forZ {A : Type}
           (z_min z_iter : Z) (f : Z -> A) : list A :=
  snd (Z.iter z_iter (fun '(z', xs) =>
    let z' := Z.pred z' in
    (z', f z' :: xs)) ((z_min + z_iter)%Z, [])).

Example forZ_ex : forZ (-1) 3 (fun x => x) = [-1; 0; 1]%Z.
Proof. reflexivity. Qed.

Definition render {A : Type} (a : A)
           (y_min y_height x_min x_width : Z)
           (g : Grid A)
  : list (list A) :=
  forZ y_min y_height (fun y =>
  forZ x_min x_width  (fun x =>
    index' a g y x)).

End GridZ.
