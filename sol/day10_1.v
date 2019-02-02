(* Inputs, first five integers on each line:

   - time to predict;
   - [x_min]
   - [x_width]
   - [y_min]
   - [y_height]

   Followed by the actual problem input.

   Some trial and error is still necessary to find the right area.

   TODO: automate, e.g., pick two arbitrary points and find when
   they are close.
 *)

From Coq Require Import
     Ascii String
     List NArith ZArith
     extraction.ExtrOcamlIntConv.
Import ListNotations.

From ExtLib Require Import
     Structures.Monad
     Structures.MonadFix.

From SimpleIO Require Import SimpleIO IO_Unsafe.

From advent Require Import lib.

(* Throws exceptions! *)
Parameter parse : forall {P V : Type},
  (int -> int -> P) ->
  (int -> int -> V) ->
  ocaml_string -> (P * V).
Extract Constant parse =>
  "fun point velo s ->
     Scanf.sscanf s ""position=< %d , %d > velocity=< %d , %d >""
       (fun px py vx vy -> (point px py, velo vx vy))".

Section main.
Import MonadNotation.
Local Open Scope monad.

Context {m : Type -> Type} `{Monad m} `{MonadFix m} `{MonadError m}
        `{MonadI ocaml_string m}
        `{MonadO ocaml_string m}.

Definition do_read {A : Type} (f : ocaml_string -> A) : m A :=
  ox <- read;;
  match ox with
  | None => error "oops"
  | Some x => ret (f x)
  end.

Definition pair_Z : int -> int -> Z * Z :=
  fun x y => (z_of_int x, z_of_int y).

Definition parse_Z : ocaml_string -> Z :=
  fun s => z_of_int (unsafe_int_of_ostring s).

Definition predict_grid {A : Type} (a : A)
           (t : Z) (ps : list ((Z * Z) * (Z * Z))) : Grid A :=
  fold_left
    (fun g p =>
      match p with
      | ((x, y), (vx, vy)) =>
        GridZ.insert (y + t * vy) (x + t * vx) a g
      end)
    ps
    (empty_grid A).

Definition main : m unit :=
  t <- do_read parse_Z;;
  x_min <- do_read parse_Z;;
  x_width <- do_read parse_Z;;
  y_min <- do_read parse_Z;;
  y_height <- do_read parse_Z;;
  lines <- read_all;;
  let points : list ((Z * Z) * (Z * Z)) := map (parse pair_Z pair_Z) lines in
  let g := predict_grid (char_of_ascii "#") t points in
  for' (GridZ.render (char_of_ascii ".")
                     y_min y_height x_min x_width g)
       (fun line =>
          print (OString.of_list line)).

End main.

Import SimpleIO.
Definition exe : io_unit := IO.unsafe_run main.
Extraction "day10_1.ml" exe.
