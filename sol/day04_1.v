(* The input for this one is assumed to be sorted (e.g., using
   the [sort] command). *)

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
Module NMap := FMapAVL.Make N_as_OT.

(* Minutes since midnight. *)
Definition time : Type := N.

(* We assume shifts happen around midnight. *)
Variant event : Type :=
| Shift (guard : N)
| FallsAsleep
| WakesUp
.

(* A list of 1 in the interval [[n1; n2-1]] *)
Definition interval (n1 n2 : N) : list nat :=
  N.iter n1 (cons 0) (N.iter (n2 - n1) (cons 1) []).

Fixpoint union {A : Type}
         (merge : A -> A -> A) (xs ys : list A) : list A :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xs, y :: ys => merge x y :: union merge xs ys
  end.

Definition union1 : list nat -> list nat -> list nat := union plus.

Parameter err : forall {A}, A.
Extract Inlined Constant err => "assert false".

Fixpoint record_sleeps_aux (r : NMap.t (list nat))
         (guard0 : N) (es : list (time * event)) : NMap.t (list nat) :=
  match es with
  | (_, Shift guard) :: es => record_sleeps_aux r guard es
  | (i, FallsAsleep) :: (j, WakesUp) :: es =>
    let gz := match NMap.find guard0 r with
              | None => []
              | Some gz => gz
              end in
    let r' := NMap.add guard0 (union1 (interval i j) gz) r in
    record_sleeps_aux r' guard0 es
  | [] => r
  | _ => err
  end.

Definition record_sleeps
           (es : list (time * event)) : NMap.t (list nat) :=
  record_sleeps_aux (NMap.empty _) 0 es.

Definition sum : list nat -> nat :=
  fun ns => fold_left plus ns 0.

Definition NMap_argmax {A : Type} (f : A -> nat)
           (r : NMap.t A) : nat * list (N * A) :=
  NMap.fold (fun i x best =>
    let y := f x in
    if y <? fst best then
      best
    else if y =? fst best then
      (fst best, (i, x) :: snd best)
    else
      (y, [(i, x)])) r (0, []).

(* Find the maximum of a list and all indices where it is reached. *)

Fixpoint arg_max_aux (best : nat) (arg : list nat) (i : nat)
         (xs : list nat) : nat * list nat :=
  match xs with
  | [] => (best, arg)
  | x :: xs =>
    if x <? best then
      arg_max_aux best arg (S i) xs
    else if x =? best then
      arg_max_aux best (i :: arg) (S i) xs
    else
      arg_max_aux x [i] (S i) xs
  end.

Definition arg_max : list nat -> nat * list nat :=
  arg_max_aux 0 [] 0.

(* Find the laziest guards (there should be only one in the AoC
   input), together with the total time they slept. *)
Definition laziest1 :
  NMap.t (list nat) -> nat * list (N * list nat) :=
  NMap_argmax sum.

Definition laziest2 :
  NMap.t (list nat) -> nat * list (N * (nat * list nat)) :=
  fun r => NMap_argmax (fun '(max_slept, _) => max_slept)
                       (NMap.map arg_max r).

Definition all_laziest1 (es : list (time * event)) :
  nat * list (N * nat * list nat) :=
  let r := record_sleeps es in
  let '(max_sleep, offenders) := laziest1 r in
  let most_slept_minutes := fun '(guard, slept) =>
    let '(m, mns) := arg_max slept in
    (guard, m, mns) in
  (max_sleep, map most_slept_minutes offenders).

Definition all_laziest2 (es : list (time * event)) :
  nat * list (N * list nat) :=
  let r := record_sleeps es in
  let '(max_slept, offenders) := laziest2 r in
  let most_slept_minutes := fun '(guard, (_, mns)) =>
    (guard, mns) in
  (max_slept, map most_slept_minutes offenders).

Section main.

Import SimpleIO.

Context {m : Type -> Type} `{Monad m} `{MonadFix m}
        `{MonadI (time * event) m}
        `{MonadO ocaml_string m}.

Infix "+++" := ostring_app (at level 30).

Definition print_all_laziest1 (a : nat * list (N * nat * list nat)) :=
  let '(max_sleep, offenders) := a in
  print (to_ostring "Total slept:");;
  print (ostring_of_int (int_of_nat max_sleep));;
  let of_n n := ostring_of_int (int_of_n n) in
  let of_nat n := ostring_of_int (int_of_nat n) in
  for' offenders (fun '(guard, max_slept, mns) =>
    print (OString.concat (to_ostring "; ") ([
      of_n guard;
      of_nat max_slept;
      OString.concat (to_ostring ",")
        (map (fun n => OString.concat (to_ostring ":") [
                of_nat n;
                of_n (guard * N.of_nat n)%N])
             mns)]
      ))
  ).

Definition print_all_laziest2 (a : nat * list (N * list nat)) :=
  let '(max_sleep, offenders) := a in
  print (to_ostring "Max slept:");;
  print (ostring_of_int (int_of_nat max_sleep));;
  let of_n n := ostring_of_int (int_of_n n) in
  let of_nat n := ostring_of_int (int_of_nat n) in
  for' offenders (fun '(guard, mns) =>
    print (OString.concat (to_ostring "; ") ([
      of_n guard;
      OString.concat (to_ostring ",")
        (map (fun n => OString.concat (to_ostring ":") [
                of_nat n;
                of_n (guard * N.of_nat n)%N])
             mns)]
      ))
  ).

Definition main1 : m unit :=
  es <- read_all;;
  let a := all_laziest1 es in
  print_all_laziest1 a.

Definition main2 : m unit :=
  es <- read_all;;
  let a := all_laziest2 es in
  print_all_laziest2 a.

End main.

Module io.

Import SimpleIO.
Import IO.Notations.

(* Partial function!? *)
Parameter parse_event : forall {TIME EVENT : Type},
    (int -> TIME) ->
    (int -> EVENT) -> EVENT -> EVENT ->
    ocaml_string -> TIME * EVENT.

Extract Constant parse_event =>
  "fun mk_time mk_shift sleep wakeup s ->
   try
     Scanf.sscanf s ""[1518-%_d-%_d %_d:%d] %[^\n]""
       (fun mn e ->
          (mk_time mn, match e with
               | ""falls asleep"" -> sleep
               | ""wakes up"" -> wakeup
               | _ -> Scanf.sscanf e ""Guard #%d"" mk_shift)
       )
   with End_of_file ->
    failwith (Printf.sprintf ""Parse error: %S"" s)".

Instance MonadI_event_IO : MonadI (time * event) IO := {
  read := catch_eof (
    s <- read_line';;
    ret (parse_event
           n_of_int
           (fun g => Shift (n_of_int g)) FallsAsleep WakesUp
           s));
}.

End io.

Import SimpleIO.

Definition exec1 : io_unit := IO.unsafe_run main1.
Extraction "day04_1.ml" exec1.

Definition exec2 : io_unit := IO.unsafe_run main2.
Extraction "day04_2.ml" exec2.
