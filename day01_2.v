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
    first_dup n (psums xs) ->
    rel_spec Z Z main zs [Str_nth n (psums xs)].

Lemma ZSet_In_add z z' s :
  ZSet.In z (ZSet.add z' s) <-> z = z' \/ ZSet.In z s.
Proof.
  split.
  - destruct (Z_as_OT.eq_dec z z').
    + auto.
    + right; eapply ZSet.add_3; eauto.
  - intros [].
    + apply ZSet.add_1; auto.
    + apply ZSet.add_2; auto.
Qed.

Lemma or_iff_distrib :
  forall A B C D, (A <-> C) -> (B <-> D) -> (A \/ B <-> C \/ D).
Proof.
  firstorder.
Qed.

Theorem search_rel (s0 : io_state Z Z) xs n :
  first_dup n (psums xs) ->
  search xs s0 s0 (Str_nth n (psums xs)).
Proof.
  intros Hdup.
  unfold search.
  match goal with
  | [ |- mfix ?body _ _ _ _ ] =>
    assert (H : forall
               seen pos pre_xs suf_xs s0 i
               (Hi : i <= n)
               (Hpre : pre_xs = Str_take i (psums xs))
               (Hsuf : suf_xs = Str_nth_tl i xs)
               (Hseen : forall x,
                   ZSet.In x seen <-> List.In x pre_xs)
               (Hpos : pos = Str_nth i (psums xs))
             ,
               lfp_rel1 body (seen, pos, suf_xs) s0 s0 (Str_nth n (psums xs)))
  end.
  { intros. remember (n - i) as ni eqn:e_ni.
    generalize dependent seen.
    generalize dependent pos.
    generalize dependent pre_xs.
    generalize dependent suf_xs.
    generalize dependent s0.
    generalize dependent i.
    induction ni as [| ni IH]; intros;
      apply lfp_rel_fold;
      destruct suf_xs as [x suf_xs].
    - assert (i = n); [| subst i].
      { symmetry in e_ni. apply Nat.sub_0_le in e_ni.
        apply Nat.le_antisymm; auto. }
      rewrite ZSet.mem_1.
      + simpl; auto.
      + destruct Hdup as [Hdup _].
        apply Hseen.
        rewrite Hpos, Hpre.
        auto.
    - assert (Hi' : i < n).
      { apply lt_O_minus_lt.
        rewrite <- e_ni.
        apply Nat.lt_0_succ.
      }
      assert (Hmem : ZSet.mem pos seen = false).
      { destruct Hdup as [Hdup Hnodup].
        apply Bool.not_true_is_false.
        intro Hmem_contra.
        apply ZSet.mem_2 in Hmem_contra.
        eapply Hnodup; eauto.
        unfold dup.
        rewrite <- Hpre, <- Hpos.
        apply Hseen; auto.
      }
      rewrite Hmem.
      eapply IH with (i := S i); auto.
      + rewrite Nat.sub_succ_r, <- e_ni; auto.
      + rewrite Str_nth_tl_S, <- Hsuf.
        reflexivity.
      + unfold psums.
        rewrite Str_scanl_S.
        f_equal; auto.
        apply (f_equal (@hd _)) in Hsuf; auto.
      + intro z. rewrite ZSet_In_add.
        rewrite Hseen.
        rewrite Str_take_S.
        rewrite in_app_iff.
        rewrite or_comm.
        rewrite <- Hpre.
        rewrite <- Hpos.
        simpl.
        intuition.
  }
  simpl in *.
  apply H with (pre_xs := []) (i := 0); auto.
  { apply Nat.le_0_l. }
  { intro x.
    split.
    - intros Hno_seen; inversion Hno_seen.
    - contradiction.
  }
Qed.

Theorem correct_main : correct main.
Proof.
  intros zs xs n Hzs Hn.
  unfold rel_spec.
  exists (Mk_io_state [] [Str_nth n (psums xs)]).
  split; [| auto].
  unfold main.
  exists xs, (Mk_io_state [] []); split.
  { (* parse_stream *)
    unfold parse_stream.
    exists zs, (Mk_io_state [] []); split.
    { (* read_all *) apply read_all_rel; auto. }
    { rewrite Hzs; simpl; auto. }
  }
  exists (Str_nth n (psums xs)), (Mk_io_state [] []); split.
  { (* search *)
    apply search_rel; auto.
  }
  simpl; auto.
Qed.

End spec.
