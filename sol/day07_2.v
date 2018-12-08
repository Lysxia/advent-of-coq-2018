
Set Warnings "-extraction-opaque-accessed".

From Coq Require Import
     List Arith NArith ZArith Ascii String
     OrderedTypeEx FSetAVL FMapAVL
     extraction.ExtrOcamlIntConv
     Lia.
Import ListNotations.

From SimpleIO Require SimpleIOUnsafe RawChar.

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

Definition Time : Type := N.

(* A pair [(t, tasks)] means all tasks in the list [tasks] complete
   at time [t]. *)
Definition WorkerEvents : Type := list (Time * list Task).

(* Definition WorkerEvents : Type := NMap.t (list Task). *)
(* Map is missing min_elt *)

Fixpoint we_insert (time : Time) (task : Task) (we : WorkerEvents) :
  WorkerEvents :=
  match we with
  | [] => [(time, [task])]
  | (time', tasks') as t' :: we' =>
    match N_as_OT.compare time time' with
    | OrderedType.LT _ => (time, [task]) :: we
    | OrderedType.EQ _ => (time, task :: tasks') :: we'
    | OrderedType.GT _ => t' :: we_insert time task we'
    end
  end.

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

Class TaskDuration : Type :=
  task_duration : Task -> Time.

Module Import DB.
Import RawChar.
(* TODO send to simple-io. *)
Definition debug_switch := false. (* Switch this to [true] for debug
                                     output. *)
Parameter debug' : forall {A}, ocaml_string -> int -> A -> A.
Extract Constant debug' => "fun s n x -> Printf.printf ""%s: %d\n"" s n; x".
Definition debug : forall {A}, string -> int -> A -> A :=
  fun _ s => if debug_switch then debug' (to_ostring s)
             else fun _ x => x.
End DB.

Section algo.

Context `{TaskDuration}.

Fixpoint assign_tasks (cur_time : Time) (n_idle : nat)
         (we : WorkerEvents) (q : TaskQueue) :
  (nat * WorkerEvents * TaskQueue) :=
  match n_idle, NSet.min_elt q with
  | O, _ | _, None => (n_idle, we, q)
  | S n_idle, Some task =>
    let q := debug "idle" (int_of_nat n_idle) (debug "assign" (int_of_n task)) (NSet.remove task q) in
    let we := we_insert
                (cur_time + task_duration task)%N task we in
    assign_tasks cur_time n_idle we q
  end.

Fixpoint order_tasks'
         (edges : Edges')
         (cur_time : Time)
         (n_tasks : nat)
         (n_idle : nat)
         (we : WorkerEvents)
         (q : TaskQueue)
         (bt : BlockingTasks) : Time :=
  let '(n_idle, we, q) := assign_tasks cur_time n_idle we q in
  match n_tasks, we with
  | O, _ | _, [] => cur_time
  | S n_tasks, (cur_time, tasks) :: we =>
    let '(q, bt) := fold_left (fun qbt task =>
        fold_left (fun '(q, bt) t' =>
          let '(i, bt) := decrement_and_get t' bt in
          if (i =? 0)%N then
            debug "Free" (int_of_n t')
            (NSet.add t' q, bt)
          else
            (q, bt)) (edges task) qbt) tasks (q, bt) in
    order_tasks' edges (debug "Compl" (int_of_n cur_time) cur_time)
                 n_tasks (List.length tasks + n_idle)
                 we q bt
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

Definition we_initial : WorkerEvents := [].

Definition order_tasks (n_idle : nat) (edges : Edges) : Time :=
  let bt := count_blocking edges in
  order_tasks' (collect_edges edges)
               0%N
               (List.length edges)
               n_idle
               we_initial
               (initial_tasks edges bt)
               bt.

End algo.

Section main.

(* N.B.: TaskDuration and n_idle hardcoded here. *)

(* [task] is the ASCII code of its name (a single char),
   and we want ['A' -> 61], ['B' -> 62], etc. *)
Instance TD : TaskDuration :=
  fun (task : Task) => (task - 4)%N : Time.

Context {m : Type -> Type} `{Monad m}
        `{FoldRead Edge m} `{MonadO N m}.

Definition main : m unit :=
  edges <- read_all;;
  print (order_tasks (* n_idle:= *) 5 edges).

End main.

Import SimpleIOUnsafe RawChar.

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
    s <- read_line';;
    '(i, j) <- parse_line s;;
    (ret (MkEdge (noc i) (noc j))));
}.

Definition exe : io_unit := IO.unsafe_run main.

Extraction "day07_2.ml" exe.

(*
  -->A--->B--
 /    \      \
C      -->D----->E
 \           /
  ---->F-----

  0    C
 63(C) A F
124(A) B D
129(F)
186(B)
188(D) E
253(E)
*)
