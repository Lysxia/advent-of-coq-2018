From Coq Require Import
     List ZArith Ascii String Streams
     OrderedTypeEx FSetAVL
     extraction.ExtrOcamlIntConv.
Import ListNotations.

From SimpleIO Require
     IOMonad CoqPervasives.

From ExtLib Require Import
     Structures.Monads.
Import MonadNotation.
Local Open Scope monad.

From advent Require Import lib.

Module ZSet := FSetAVL.Make Z_as_OT.

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

Section main.

Context {m : Type -> Type}
        `{Monad m} `{MonadError m}
        `{MonadI Z m} `{MonadO Z m} `{MonadFix m}.

Definition parse_stream : m (Stream Z) :=
  zs <- read_all;;
  match cycle zs with
  | None => error "empty input"
  | Some s => ret s
  end.

Definition no_seen : ZSet.t := ZSet.empty.

Definition search (s : Stream Z) : m Z :=
  mfix (fun loop '(seen, pos, (Cons z s)) =>
    if ZSet.mem pos seen then
      ret pos
    else
      loop (ZSet.add pos seen, (pos + z)%Z, s)
  ) (no_seen, 0%Z, s).

Definition main : m unit :=
  s <- parse_stream;;
  z <- search s;;
  print z.

End main.

Import SimpleIO.IOMonad.

Definition exec : io_unit := unsafe_run main.

Extraction "day01_2.ml" exec.


Section spec.

(* Stream of partial sums: we get the actual frequencies from
   a stream of frequency changes. *)
Definition psums : Stream Z -> Stream Z :=
  Str_scanl Z.add 0%Z.

(*
(* [all_distinct xs]: the elements of [xs] are all distinct from
   each other. *)
Definition all_distinct {A : Type} (xs : list A) : Prop :=
  forall pre x suf,
    xs = pre ++ x :: suf ->
    ~List.In x pre /\ ~List.In x suf.
*)

(* [dup n xs]: The [n]-th element of [xs] already occured before. *)
Definition dup {A : Type} (n : nat) (xs : Stream A) : Prop :=
  List.In (Str_nth n xs) (Str_take n xs).

(* [first_dup n xs]: The [n]-th element is the first duplicate. *)
Definition first_dup {A : Type} (n : nat) (xs : Stream A) : Prop :=
  dup n xs /\
  forall m, m < n -> ~ dup m xs.

(* [main] outputs the value of the first duplicate, if there is one. *)
Definition correct (main : io_rel Z Z unit) : Prop :=
  forall zs xs n,
    cycle zs = Some xs ->
    first_dup n xs ->
    rel_spec Z Z main zs [Str_nth n xs].

Fixpoint Str_drop {A : Type} (n : nat) (xs : Stream A) : Stream A :=
  match n, xs with
  | O, _ => xs
  | S n, Cons _ xs => Str_drop n xs
  end.

Theorem correct_main : correct main.
Proof.
  intros zs xs n Hzs Hn.
  unfold rel_spec.
  exists (Mk_io_state [] [Str_nth n xs]).
  split; [| auto].
  unfold main.
  exists xs, (Mk_io_state [] []); split.
  { (* parse_stream *)
    unfold parse_stream.
    exists zs, (Mk_io_state [] []); split.
    { (* read_all *) apply read_all_rel; auto. }
    { rewrite Hzs; simpl; auto. }
  }
  exists (Str_nth n xs), (Mk_io_state [] []); split.
  { (* search *)
    unfold search.
    match goal with
    | [ |- mfix ?body _ _ _ _ ] =>
      assert (H : forall
                 seen pos pre_xs suf_xs s0 i
                 (Hpre : pre_xs = Str_take i (psums xs))
                 (Hsuf : suf_xs = Str_drop i xs)
                 (Hseen : forall x,
                     ZSet.In x seen <-> List.In x pre_xs)
                 (Hpos : pos = Str_nth i (psums xs))
                 ,
                 mfix body (seen, pos, suf_xs) s0 s0 (Str_nth n xs))
    end.
    {
      admit.
    }
    apply H with (pre_xs := []) (i := 0); auto.
    { intro x.
      split.
      - intros Hno_seen; inversion Hno_seen.
      - contradiction.
    }
  }
  simpl; auto.
Abort.

End spec.
