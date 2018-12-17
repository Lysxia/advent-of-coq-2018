(* Two solutions are implemented, with n = nb of rectangles
   (i.e., input size):
   - [day03_1_simple.ml], naive O(grid_size * n)
   - [day03_1.ml], O(n log(n))
 *)

Set Warnings "-extraction-opaque-accessed".

From Coq Require Import
     List Arith NArith ZArith Ascii String
     OrderedTypeEx FSetAVL FMapAVL
     extraction.ExtrOcamlIntConv
     Lia.
Import ListNotations.

From SimpleIO Require SimpleIO.

From ExtLib Require Import
     Structures.Monads.
Import MonadNotation.
Local Open Scope monad.

From advent Require Import lib.

(* Sets indexed by natural numbers. *)
Module NatSet := FSetAVL.Make Nat_as_OT.

(* Maps indexed by (binary) natural numbers. *)
Module NMap := FMapAVL.Make N_as_OT.


(* A naive solution. *)

Variant rectangle : Type :=
| Rectangle (id : N) (left top width height : N)
.

Definition matrix := list (list nat).

Definition rectangle_matrix (r : rectangle) : matrix :=
  let '(Rectangle _ l t w h) := r in
  let row := N.iter l (cons 0) (N.iter w (cons 1) []) in
  N.iter t (cons []) (N.iter h (cons row) []).

Fixpoint union {A : Type}
         (merge : A -> A -> A) (xs ys : list A) : list A :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xs, y :: ys => merge x y :: union merge xs ys
  end.

Definition union1 : list nat -> list nat -> list nat := union plus.
Definition union2 : matrix -> matrix -> matrix := union union1.

Definition union_rectangles (rs : list rectangle) : matrix :=
  fold_left (fun x r => union2 x (rectangle_matrix r)) rs [].

Definition count_overlaps (x : matrix) : N :=
  fold_left (fun p row =>
    fold_left (fun p c => if 2 <=? c then (1 + p)%N else p) row p)
    x 0%N.

(* Then [fun rs : rectangle => count_overlaps (union_rectangles rs)]
   computes the expected answer: the area of the plane covered by
   at least two rectangles in [rs]. *)


(* A less naive solution. *)

(* First, there's a neat scanning algorithm bounding the complexity
   by O(matrix_sz + n_rectangles) (with an extra log factor because
   we don't have O(1) random access), but we can also avoid a boring
   array iteration by only traversing rectangle corners.
   We get O(n log(n)) where n = n_rectangles.
 *)

(* The high-level idea is thus: put 1 and -1 on/near the corners of
   a rectangle (i,j)×(a,b) as follows (the top row and leftmost
   column are coordinate axes, every other entry in the matrix is 0):

       i       j  j+1

  a    1 0 ... 0  -1
       0           0
       .           .
       .           .
  b    0           0
  b+1 -1 0 ... 0   1

   then, 1. do a scan (cumulative sum) for each column,
         2. do a scan for each row of the matrix resulting from 1,
   that fills the rectangle with 1, and sets the rest of the
   matrix to 0.

       i       j  j+1
  a    1 1 ... 1   0
       .       .   .
       .       .   .
       .       .   .
  b    1 1 ... 1   0
  b+1  0   ... 0   0

   this formula is linear, so that if you add multiple rectangles
   in the same matrix, the scan will give you a matrix where each
   entry says how many rectangles contain it.
 *)

(* A sparse infinite matrix as a map [N -> N -> Z] ([N * N -> Z]),
   where all unbound keys are mapped to 0. *)
Definition smatrix := NMap.t (NMap.t Z).

(* Modify the entry at row [i], column [j]. *)
Definition set_point (f : Z -> Z) (i j : N) (x : smatrix) : smatrix :=
  let '(row, u') :=
      match NMap.find i x with
      | None => (NMap.empty _, f 0%Z)
      | Some row => (row, match NMap.find j row with
                          | None => f 0%Z
                          | Some u => f u
                          end)
      end in
  NMap.add i (NMap.add j u' row) x.

(* Print a rectangle into the matrix. *)
Definition add_rectangle (r : rectangle) (x : smatrix) : smatrix :=
  let '(Rectangle _ l t w h) := r in
  set_point Z.succ t l (
  set_point Z.pred t (l + w) (
  set_point Z.pred (t + h) l (
  set_point Z.succ (t + h) (l + w) x))).

Definition sunion_rectangles (rs : list rectangle) : smatrix :=
  fold_left (fun x r => add_rectangle r x) rs (NMap.empty _).

Definition Row : Type := list (N * Z).

Notation conspair' i z t :=
  (if (z =? 0)%Z then
     t
   else
     (i, z%Z) :: t).

Fixpoint add_rows (r1 r2 : list (N * Z)) : list (N * Z) :=
  match r1 with
  | [] => r2
  | (i1, z1) :: tl_r1 =>
    let fix add_row2 r2 :=
        match r2 with
        | [] => r1
        | (i2, z2) :: tl_r2 =>
          match N_as_OT.compare i1 i2 with
          | OrderedType.LT _ =>
            conspair' i1 z1 (add_rows tl_r1 r2)
          | OrderedType.EQ _ =>
            let z' := (z1 + z2)%Z in
            conspair' i1 z' (add_rows tl_r1 tl_r2)
          | OrderedType.GT _ =>
            conspair' i2 z2 (add_row2 tl_r2)
          end
        end in
    add_row2 r2
  end.

(* Scan a row, looking for areas covered by overlapping rectangles
   (z0 > 2). *)
Fixpoint scan_row_aux
         (n : N) (i0 : N) (z0 : Z) (r : list (N * Z)) : N :=
  match r with
  | [] => n
  | (i, z) :: r =>
    let n' := if (2 <=? z0)%Z then (n + i - i0)%N else n in
    scan_row_aux n' i (z0 + z)%Z r
  end.

Definition scan_row : list (N * Z) -> N := scan_row_aux 0 0 0.

(* 0         5         0
   0 0 2 0 0-1 0 0 0 0 1-2 (row)
   0 0 2 2 2 1 1 1 1 1 2 0 (scanned row) (four 2's)
 *)

Example scan_row_ex :
  scan_row [(2%N, 2%Z); (5%N, (-1)%Z); (10%N, 1%Z); (11%N, (-2)%Z)]
  = 4%N.
Proof. reflexivity. Qed.

Fixpoint scan_aux
         (n : N) (r0 : list (N * Z))
         (rs : list (N * list (N * Z))) : N :=
  match rs with
  | (i1, r1) :: ((i2, _) :: _) as rs =>
    let r1' := add_rows r0 r1 in
    scan_aux (n + (i2 - i1) * scan_row r1') r1' rs
  | [_] | [] => n (* The last row should be empty *)
  end.

Definition scan : list (N * list (N * Z)) -> N := scan_aux 0 [].

Definition count_overlaps2 (rs : list rectangle) : N :=
  scan (NMap.elements
          (NMap.map (@NMap.elements _)
                    (sunion_rectangles rs))).

(* For debugging. *)
Section debug.

Context {m : Type -> Type} `{Monad m} `{MonadFix m}
        `{MonadI rectangle m}
        `{MonadO (list ascii) m}.

Definition print_matrix (x : matrix) : m unit :=
  for' x (fun row =>
    print (map (fun n =>
      match n with
      | 0 => "0"
      | 1 => "1"
      | 2 => "2"
      | 3 => "3"
      | 4 => "4"
      | 5 => "5"
      | _ => "#"
      end%char) row)).

Definition show_matrix (w h : nat) : m unit :=
  rs <- read_all;;
  let x := fold_left
             (fun m r => union2 m (rectangle_matrix r)) rs [] in
  print_matrix (map (firstn w) (firstn h x)).

End debug.

Section main.

Context {m : Type -> Type} `{Monad m} `{MonadFix m}
        `{MonadI rectangle m}
        `{MonadO N m}.

Definition main1 : m unit :=
  rs <- read_all;;
  print (count_overlaps (union_rectangles rs)).

Definition main2 : m unit :=
  rs <- read_all;;
  print (count_overlaps2 rs).

End main.

Module io.

Import SimpleIO.
Import IO.Notations.

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

Import SimpleIO.

(* DEBUG *)
(*
Definition show_matrix_exec : io_unit := unsafe_run (show_matrix 0 0).
Extraction "day03_1_show_matrix.ml" show_matrix_exec.
*)

Definition exec1 : io_unit := IO.unsafe_run main1.
Extraction "day03_1_basic.ml" exec1.

Definition exec2 : io_unit := IO.unsafe_run main2.
Extraction "day03_1.ml" exec2.

(* We first verify the naive solution. *)

(* Points are given by their coordinates; shapes are sets of points. *)
Definition point : Type := nat * nat.
Definition shape : Type := point -> Prop.
Definition eq_shape (s1 s2 : shape) : Prop :=
  forall p, s1 p <-> s2 p.

(* And of course, rectangles are shapes. *)
Definition rectangle_shape (r : rectangle) : shape :=
  let '(Rectangle _ l t w h) := r in
  fun p => N.to_nat l <= fst p < N.to_nat l + N.to_nat w /\
           N.to_nat t <= snd p < N.to_nat t + N.to_nat h.

Lemma sumbool_right_de_morgan P Q R :
  { P } + { ~ Q \/ ~ R } -> { P } + { ~ (Q /\ R) }.
Proof. firstorder. Qed.

Definition rectangle_shape_dec (r : rectangle) (p : point) :
  {rectangle_shape r p} + {~ rectangle_shape r p}.
Proof.
  destruct r; simpl.
  repeat (apply sumbool_right_de_morgan; apply Sumbool.sumbool_and);
    apply le_dec.
Qed.

Definition sum (xs : list nat) : nat :=
  fold_left plus xs 0.

(* This function counts the number of rectangles in a list [rs]
   covering a given point [p]. *)
Definition count_covering_rectangles
           (rs : list rectangle) (p : point) : nat :=
  sum (map (fun r => if rectangle_shape_dec r p then 1 else 0) rs).

Definition matrix_ix (x : matrix) (p : point) : nat :=
  nth (fst p) (nth (snd p) x []) 0.

(* Matrices produced by [rectangle_points] define shapes too. *)
Definition matrix_shape (x : matrix) : shape :=
  fun p => 0 < matrix_ix x p.

Ltac simpl_length :=
  repeat rewrite repeat_length in *.

Ltac split_nth :=
  match goal with
  | [ |- context [nth ?x (app ?t1 ?t2)] ] =>
    let Hx := fresh "Hx" in
    destruct (Nat.lt_ge_cases x (List.length t1)) as [Hx | Hx];
    [ rewrite app_nth1 with (n := x)
    | rewrite app_nth2 with (n := x)
    ]
  | [ |- context [ nth ?m (repeat ?a ?n) ?b ]] =>
    let Hl := fresh "Hl" in
    destruct (Nat.lt_ge_cases m n) as [Hl | Hl];
    [ rewrite (repeat_nth1 m n a b)
    | rewrite (repeat_nth2 m n a b)
    ]
  | [ |- context [ nth ?m [] ?b ]] =>
    rewrite nth_nil
  end; auto; simpl_length.

Lemma rectangle_shape_matrix1 (r : rectangle) (p : point) :
  rectangle_shape r p -> matrix_ix (rectangle_matrix r) p = 1.
Proof.
  destruct r, p as [i j].
  unfold matrix_ix; simpl.
  repeat rewrite N2Nat.inj_iter.
  repeat rewrite iter_cons.
  intros [[Hleft Hwidth] [Htop Hheight]].
  repeat
    ((rewrite repeat_nth1 + rewrite app_nth2 + rewrite app_nth1);
     simpl_length; [|lia]).
    lia.
Qed.

Lemma rectangle_shape_matrix2 (r : rectangle) (p : point) :
  ~rectangle_shape r p -> matrix_ix (rectangle_matrix r) p = 0.
Proof.
  destruct r, p as [i j].
  unfold matrix_ix; simpl.
  repeat rewrite N2Nat.inj_iter.
  repeat rewrite iter_cons.
  intros H.
  repeat split_nth.
  exfalso; apply H; lia.
Qed.

(* [matrix_ix] is a monoid homomorphism, between [union2] and [plus].
 *)

Lemma matrix_ix_hom x1 x2 p :
  matrix_ix (union2 x1 x2) p = matrix_ix x1 p + matrix_ix x2 p.
Proof.
  destruct p as [i j].
  revert x1; revert x2.
  revert i. unfold matrix_ix.
  simpl.
  induction j.
  - destruct x1 as [ | t1 x1 ], x2 as [ | t2 x2];
      repeat rewrite nth_nil; simpl; auto.
    destruct i; auto.
    clear. revert t2; revert t1.
    induction i.
    + destruct t1, t2; simpl; auto.
    + destruct t1, t2; simpl; auto.
  - destruct x1, x2; repeat rewrite nth_nil; simpl; auto.
    destruct i; auto.
Qed.

Theorem union_rectangles_count rs p :
  matrix_ix (union_rectangles rs) p = count_covering_rectangles rs p.
Proof.
  unfold union_rectangles.
  pose proof
       (fold_left_hom
          (fun x r => union2 x (rectangle_matrix r))
          (fun n r => n + if rectangle_shape_dec r p then 1 else 0)
          (fun x => matrix_ix x p)).
  simpl in H; rewrite H; clear H.
  { rewrite fold_left_map. unfold count_covering_rectangles.
    unfold matrix_ix; repeat rewrite nth_nil; auto.
  }
  { intros; rewrite matrix_ix_hom.
    destruct rectangle_shape_dec.
    - rewrite rectangle_shape_matrix1; auto.
    - rewrite rectangle_shape_matrix2; auto.
  }
Qed.
