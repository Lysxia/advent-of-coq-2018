From Coq Require Import
     String List ZArith
     extraction.ExtrOcamlIntConv.
Import ListNotations.

From ExtLib Require Import
     Structures.Monad.
Import MonadNotation.
Local Open Scope monad.

From SimpleIO Require Import SimpleIO.

From advent Require Import lib.

Inductive nanobot : Type := Nanobot (x y z r : Z).

Parameter read_nanobot' :
  forall r : Type, (int -> int -> int -> int -> r) -> IO r.
Extract Constant read_nanobot' => "
  fun f k ->
    k (Scanf.scanf ""pos=<%d,%d,%d>, r=%d "" f)".

Definition read_nanobot : IO (option nanobot) :=
  catch_eof (read_nanobot' _ (fun x y z r =>
                   Nanobot (z_of_int x) (z_of_int y) (z_of_int z)
                         (z_of_int r))).

Definition range_lt : nanobot -> nanobot -> bool :=
  fun '(Nanobot _ _ _ r1) '(Nanobot _ _ _ r2) =>
    (r1 <? r2)%Z.

Fixpoint find_max_range'
         (ns0 : list nanobot) (ns : list nanobot) : list nanobot :=
  match ns with
  | [] => ns0
  | n :: ns =>
    let ns0 :=
        match ns0 with
        | [] => [n]
        | n0 :: _ => if range_lt n0 n then [n] else ns0
        end
    in find_max_range' ns0 ns
  end.

Definition find_max_range : list nanobot -> list nanobot :=
  find_max_range' [].

(* [in_range n0 n1]: nanobot [n1] is within range of nanobot [n0]. *)
Definition in_range : nanobot -> nanobot -> bool :=
  fun '(Nanobot x0 y0 z0 r0) '(Nanobot x1 y1 z1 _) =>
    (Z.abs (x0 - x1) + Z.abs (y0 - y1) + Z.abs (z0 - z1) <=? r0)%Z.

Section main.

Context {m : Type -> Type} `{Monad m} `{MonadError m}
        `{FoldRead nanobot m} `{MonadO nat m}.

Definition main : m unit :=
  ps <- read_all;;
  match find_max_range ps with
  | [] => error "no nanobots"
  | _ :: _ :: _ => error "no unique max-range nanobot"
  | [n0] =>
    print (length (filter (in_range n0) ps))
  end.

End main.

Instance MonadI_nanobot_IO : MonadI nanobot IO := {
  read := read_nanobot;
}.

Definition exe : io_unit := IO.unsafe_run main.
Extraction "day23_1.ml" exe.
