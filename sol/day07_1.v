
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

Module NMap := FMapAVL.Make N_as_OT.
Module NSet := FSetAVL.Make N_as_OT.

Definition Task : Type := N.

(* An edge [MkEdge i j] means task [i] must be completed before task
   [j]. In other words, task [j] depends on task [i]. *)
Variant Edge : Type := MkEdge : Task -> Task -> Edge.

Definition Edges : Type := list Edge.
Definition Edges' : Type := Task -> list Task. (* Adjacency lists *)

(* Map task to remaining number of tasks it depends on. *)
Definition BlockingTasks : Type := NMap.t N.

(* Available tasks, sorted by name. *)
Definition TaskQueue : Type := NSet.t.

Definition increment (task : Task) (bt : BlockingTasks) :
  BlockingTasks :=
  match NMap.find task bt with
  | None => NMap.add task 1%N bt
  | Some n => let n := (n+1)%N in NMap.add task n bt
  end.

Definition decrement_and_get (task : Task) (bt : BlockingTasks) :
  N * BlockingTasks :=
  match NMap.find task bt with
  | None => (0%N, bt) (* Should not happen. *)
  | Some n => let n := (n-1)%N in (n, NMap.add task n bt)
  end.

Fixpoint order_tasks' (edges : Edges') (n_tasks : nat)
         (q : TaskQueue) (bt : BlockingTasks) : list Task :=
  match n_tasks, NSet.min_elt q with
  | O, _ | _, None => []
  | S n_tasks, Some task =>
    let q := NSet.remove task q in
    let '(q, bt) := fold_left (fun '(q, bt) t' =>
      let '(i, bt) := decrement_and_get t' bt in
      if (i =? 0)%N then
        (NSet.add t' q, bt)
      else
        (q, bt)) (edges task) (q, bt) in
    task :: order_tasks' edges n_tasks q bt
  end.

Definition collect_edges (edges : Edges) : Edges' :=
  let edges_ := fold_left (fun edges_ '(MkEdge i j) =>
        match NMap.find i edges_ with
        | None => NMap.add i [j] edges_
        | Some js => NMap.add i (j :: js) edges_
        end) edges (NMap.empty _) in
  fun i => match NMap.find i edges_ with
           | None => []
           | Some js => js
           end.

Definition count_blocking (edges : Edges) : BlockingTasks :=
  fold_left (fun bt '(MkEdge _ j) => increment j bt)
            edges (NMap.empty _).

Definition initial_tasks (edges : Edges)
           (bt : BlockingTasks) : NSet.t :=
  fold_left (fun q '(MkEdge task _) =>
               if NMap.mem task bt then q else NSet.add task q)
            edges NSet.empty.

Definition order_tasks (edges : Edges) : list Task :=
  let bt := count_blocking edges in
  order_tasks' (collect_edges edges)
               (List.length edges)
               (initial_tasks edges bt)
               bt.

Variant Ordered : Type := MkOrdered : list Task -> Ordered.

Section main.

Context {m : Type -> Type} `{Monad m}
        `{FoldRead Edge m} `{MonadO Ordered m}.

Definition main : m unit :=
  edges <- read_all;;
  print (MkOrdered (order_tasks edges)).

End main.

Import SimpleIO.
Require Import SimpleIO.IO_Unsafe.

Parameter parse_line : ocaml_string -> IO (char * char).
Extract Constant parse_line =>
  "fun s k ->
   try
     Scanf.sscanf s
       ""Step %c must be finished before step %c can begin.""
       (fun i j -> k (i, j))
   with End_of_file ->
     failwith (Printf.sprintf ""Parse error: %S"" s)".

Definition noc (c : char) : N :=
  n_of_int (int_of_char c).
Definition con (n : N) : char :=
  unsafe_char_of_int (int_of_n n).

Instance MonadI_Edge_IO : MonadI Edge IO := {
  read := catch_eof (
    s <- read_line;;
    '(i, j) <- parse_line s;;
    (ret (MkEdge (noc i) (noc j))));
}.

Instance MonadO_Ordered_IO : MonadO Ordered IO := {
  print := fun '(MkOrdered os) =>
    print (OString.of_list (List.map con os));
}.

Definition exe : io_unit := IO.unsafe_run main.

Extraction "day07_1.ml" exe.
