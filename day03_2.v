From Coq Require Import
     List Arith NArith ZArith Ascii String
     Orders Sorting
     OrderedTypeEx FSetAVL FMapAVL
     extraction.ExtrOcamlIntConv
     Lia.
Import ListNotations.

From SimpleIO Require
     IOMonad OcamlPervasives.

From ExtLib Require Import
     Structures.Monads.
Import MonadNotation.
Local Open Scope monad.

From advent Require Import lib.

(* Sets indexed by natural numbers. *)
Module NSet := FSetAVL.Make N_as_OT.

Variant rectangle : Type :=
| Rectangle (id : N) (left top width height : N)
.

(* We sort rectangles by the position of their top side
   (remember that the Y axis points downwards). *)
Module RectangleOrder <: TotalLeBool.
  Definition t : Type := rectangle.
  Definition leb (r1 r2 : rectangle) :=
    let '(Rectangle _ _ t1 _ _) := r1 in
    let '(Rectangle _ _ t2 _ _) := r2 in
    (t1 <=? t2)%N.
  Theorem leb_total : forall r1 r2,
      leb r1 r2 = true \/ leb r2 r1 = true.
  Proof.
    intros [] []; simpl.
    destruct N.leb eqn:e; auto.
    right. apply N.leb_le, N.lt_le_incl, N.leb_gt. auto.
  Qed.
End RectangleOrder.

Module Import RectangleSort := Sort RectangleOrder.

Definition close_overlap (r1 r2 : rectangle) : bool :=
  let '(Rectangle _ l1 _ w1 _) := r1 in
  let '(Rectangle _ l2 _ w2 _) := r2 in
  ((l1 <=? l2)%N && (l2 <? l1 + w1)%N) ||
  ((l2 <=? l1)%N && (l1 <? l2 + w2)%N).

Fixpoint take_while {A : Type} (p : A -> bool) (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: xs =>
    if p x then x :: take_while p xs
    else []
  end.

(* Having sorted the list of rectangles, given a rectangle [r1]
   with top side at [t1] and with height [h1], we can first filter
   out rectangles whose top side is lower than [t1 + h1].  *)
Definition high_enough (r1 r2 : rectangle) : bool :=
  let '(Rectangle _ _ t1 _ h1) := r1 in
  let '(Rectangle _ _ t2 _ _) := r2 in
  (t2 <? t1 + h1)%N.

(* Get the identifier of a rectangle. *)
Definition id (r : rectangle) : N :=
  let '(Rectangle id _ _ _ _) := r in id.

Fixpoint search_aux
         (* Set of rectangles known to overlap with some higher one. *)
         (overlaps : NSet.t) (rs : list rectangle) : option N :=
  match rs with
  | [] => None
  | r :: rs =>
    (* List of rectangles overlapping with [r] *)
    let olapping := filter (close_overlap r)
                        (take_while (high_enough r) rs) in
    match olapping with
    | [] =>
      let i := id r in
      if NSet.mem i overlaps then
        search_aux overlaps rs
      else
        Some i
    | _ :: _ =>
      search_aux
        (fold_left (fun s x => NSet.add (id x) s) olapping overlaps)
        rs
    end
  end.

Definition search : list rectangle -> option N :=
  search_aux NSet.empty.

Section main.

Context {m : Type -> Type} `{Monad m} `{MonadFix m}
        `{MonadError m}
        `{MonadI rectangle m} `{MonadO N m}.

Definition main : m unit :=
  rs <- read_all;;
  match search (sort rs) with
  | None => error "Rectangle not found"
  | Some r => print r
  end.

End main.

Module io.

Import SimpleIO.IOMonad SimpleIO.OcamlPervasives SimpleIO.Utils.
Import IONotations.

Parameter parse_rectangle : ocaml_string -> int * int * int * int * int.
Extract Constant parse_rectangle =>
  "fun s -> Scanf.sscanf s ""#%d @ %d,%d: %dx%d""
              (fun i l t w h -> (((i, l), t), w), h)".

Instance MonadI_rectangle_IO : MonadI rectangle IO := {
  read := catch_eof (
    s <- read_line';;
    let '(i, l, t, w, h) := parse_rectangle s in
    ret (Rectangle (n_of_int i) (n_of_int l) (n_of_int t) (n_of_int w) (n_of_int h)))
}.

End io.

Import SimpleIO.IOMonad.

Definition exec : io_unit := unsafe_run main.
Extraction "day03_2.ml" exec.
