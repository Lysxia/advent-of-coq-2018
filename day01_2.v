From Coq Require Import
     List ZArith Ascii String Streams
     OrderedTypeEx FSetAVL
     extraction.ExtrOcamlIntConv.
Import ListNotations.

From SimpleIO Require Import
     IOMonad CoqPervasives Utils.

Import IONotations.

Module ZSet := FSetAVL.Make Z_as_OT.

Definition read_Z : IO Z :=
  map_io z_of_int read_int.

Definition print_Z (z : Z) : IO unit :=
  print_int (int_of_z z);;
  print_newline.

Definition cycle_aux {A} (self : Stream A) : list A -> Stream A :=
  cofix cycle_aux (xs : list A) : Stream A :=
    match xs with
    | [] => self
    | x :: xs => Cons x (cycle_aux xs)
    end.

Definition cycle {A} (xs : list A) : option (Stream A) :=
  match xs with
  | [] => None
  | x :: xs => Some (cofix res := Cons x (cycle_aux res xs))
  end.

Definition parse_stream : IO (Stream Z) :=
  fix_io (fun loop acc =>
    oz <- catch_eof read_Z;;
    match oz with
    | None =>
      match cycle (rev acc) with
      | None => prerr_endline "empty input";; exit_nat 1
      | Some s => ret s
      end
    | Some z => loop (z :: acc)
    end) [].

Definition no_seen : ZSet.t := ZSet.empty.

Definition search (s : Stream Z) : IO Z :=
  fix_io (fun loop '(seen, pos, (Cons z s)) =>
    if ZSet.mem pos seen then
      ret pos
    else
      loop (ZSet.add pos seen, (pos + z)%Z, s)
  ) (no_seen, 0%Z, s).

Definition main : IO unit :=
  s <- parse_stream;;
  z <- search s;;
  print_Z z.

Definition exec : io_unit := unsafe_run main.

Extraction "day01_2.ml" exec.

