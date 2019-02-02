(* This is actually the solution to both parts one and two
   (since the only difference is the scale of inputs).

   The expected input format is two lines, the number of players
   followed by the number of marbles (so you had to edit the
   provided input (a sentence) a little).
 *)

From Coq Require Import
     List NArith String.
Import ListNotations.

From ExtLib Require Import
     Structures.Monad.

From SimpleIO Require Import SimpleIO.

From advent Require Import lib.

Definition Zipper : Type := list N * list N.

Definition go_right : Zipper -> Zipper := fun z =>
  match z with
  | (l, []) =>
    match rev' l with
    | [] => ([], [])
    | x :: r' => ([x], r')
    end
  | (l, x :: r') => (x :: l, r')
  end.

Definition go_left : Zipper -> Zipper := fun z =>
  match z with
  | ([], r) =>
    match rev' r with
    | [] => ([], [])
    | x :: l' => (l', [x])
    end
  | (x :: l', r) => (l', x :: r)
  end.

Record Board : Type := MkBoard {
  players : Zipper;
  marbles : Zipper;
}.

(* clockwise = rightwards *)

Definition turn (next_marble : N) (board : Board) : Board :=
  let '(MkBoard ps ms) := board in
  if (N.modulo next_marble 23 =? 0)%N then
    (* We go one more step to put the 7th marble on the
       right half of the zipper *)
    match N.iter 8 go_left ms, ps with
    | (_, []), _ | _, ([], _) => board (* should not happen *)
    | (l, x :: r), (p :: pl, pr) =>
      {| players := (go_right ((next_marble + x + p)%N :: pl, pr));
         marbles := go_right (l, r);
      |}
    end
  else
    match go_right ms with
    | (l, r) =>
      {| players := go_right ps;
         marbles := (next_marble :: l, r);
      |}
    end.

Definition play (n_players max_marble : N) : Board :=
  snd (N.iter
    max_marble
    (fun '(next, bd) =>
      let next := (N.succ next)%N in
      (next, turn next bd))
    (0%N, {|
      players := (N.iter n_players (cons 0%N) [], []);
      marbles := ([0%N],[])
    |})).

(* Compute play 9 25. *)

Definition maximum (xs : Zipper) : N :=
  let '(l, r) := xs in
  fold_left N.max (l ++ r) 0%N.

Section main.
Import MonadNotation.
Local Open Scope monad.

Context {m : Type -> Type} `{Monad m} `{MonadError m}
        `{MonadI N m} `{MonadO N m}.

Definition main : m unit :=
  n_players <- read;;
  n_marbles <- read;;
  match n_players, n_marbles with
  | Some n_players, Some n_marbles =>
    let bd := play n_players n_marbles in
    print (maximum (players bd))
  | _, _ => error "Invalid input"
  end.

End main.

Import SimpleIO.
Definition exe : io_unit := IO.unsafe_run main.
Extraction "day09_1.ml" exe.
