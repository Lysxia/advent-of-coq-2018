From Coq Require Import
     List ZArith Ascii String.
Import ListNotations.

From Coq.extraction Require Import
     ExtrOcamlIntConv.

From SimpleIO Require Import
     IOMonad CoqPervasives Utils.

Import IONotations.

Definition read_Z : IO Z :=
  map_io z_of_int read_int.

Definition print_Z (z : Z) : IO unit :=
  print_int (int_of_z z);;
  print_newline.

Definition main : IO unit :=
  fix_io (fun loop z0 =>
    oz <- catch_eof read_Z;;
    match oz with
    | None => print_Z z0
    | Some z => loop (z + z0)%Z
    end) 0%Z.

Definition exec : io_unit := unsafe_run main.

Extraction "day01_1.ml" exec.
