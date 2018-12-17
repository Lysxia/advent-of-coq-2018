From Coq Require Import
     String List Arith ZArith
     FMapAVL OrderedTypeEx
     extraction.ExtrOcamlIntConv.
Import ListNotations.

From ExtLib.Structures Require Import
     Monad MonadFix.

From SimpleIO Require SimpleIO.

From advent Require Import lib sol.day16_common.

Module ZMap := FMapAVL.Make Z_as_OT.

Definition assignments : Type := ZMap.t (list op).

Definition initial_assignments : assignments :=
  snd (Z.iter 16
              (fun '(i, t) => ((i + 1)%Z, ZMap.add i all_ops t))
              (0%Z, ZMap.empty _)).

Definition show_list {A : Type}
           (show : A -> string) (xs : list A) : string :=
  "[" ++ (fix aux xs : string :=
    match xs with
    | [] => "]"
    | [x] => show x ++ "]"
    | x :: xs => show x ++ "," ++ aux xs
    end%string) xs.

Section show.
Import SimpleIO.

Definition show_z (z : Z) : string :=
  from_ostring (ostring_of_int (int_of_z z)).

Definition show_assignments (p : assignments) : string :=
  show_list
    (fun '(i, os) => show_z i ++ ":" ++ show_list show_op os)%string
    (ZMap.elements p).

Definition show_code : list (Z * op) -> string :=
  show_list (fun '(i, o) =>
                      show_z i ++ ":" ++ show_op o)%string.

End show.

Section enum.
Import SimpleIO.

Inductive stream' (A : Type) :=
| snil
| scons : A -> (unit -> stream' A) -> stream' A
.

Definition stream (A : Type) := unit -> stream' A.

Fixpoint enum_aux (os : list (Z * op)) (p : list (Z * list op)) :
  stream (list (Z * op)) -> stream (list (Z * op)) :=
  fun s (_ : unit) =>
    match p with
    | [] => scons _ (rev' os) s
    | (i, os') :: p =>
      fold_left
        (fun s o =>
           if existsb (fun '(_, o') => eqb_op o o') os then
             s
           else
             enum_aux ((i, o) :: os) p s)
        os' s tt
    end.

Definition enum p := enum_aux [] (ZMap.elements p) (fun _ => snil _).

Definition opcode_to_op (p : list (Z * op)) : Z -> op :=
  let m := fold_left
             (fun m '(i, o) => ZMap.add i o m) p (ZMap.empty _) in
  fun i =>
    match ZMap.find i m with
    | None => dummy
    | Some o => o
    end.

Variant instr : Type :=
  Instr (opcode : Z) (a b c : Z).

Definition interp_instr (oto : Z -> op) : regs -> instr -> regs :=
  fun rs '(Instr o a b c) =>
    interp (oto o, a, b, c) rs.

End enum.

Section main.

Import MonadNotation.
Local Open Scope monad_scope. 

Definition sample_ (regs instr : Type) : Type :=
  regs * instr * regs.

Definition sample : Type := sample_ regs instr.

Context {m : Type -> Type} `{Monad m} `{MonadFix m} `{MonadError m}
        `{MonadDebug m}
        `{FoldRead sample m} `{FoldRead instr m} `{MonadO Z m}.

Definition test_sample : assignments -> sample -> assignments :=
  fun p '(rs, Instr oc a b c, rs') =>
    match ZMap.find oc p with
    | None => p (* Should not happen. *)
    | Some os =>
      let os :=
          filter
            (fun o =>
               let is := (o, a, b, c) in
               wf is && eqb_reg (interp is rs) rs')%bool
            os in
      ZMap.add oc os p
    end.

Definition deduce_assignments : m assignments :=
  fold_read test_sample initial_assignments.

Import SimpleIO.

Definition check_unique {A : Type}
           (show : A -> string) (s : stream A) : m A :=
  match s tt with
  | snil _ => error "No solution"
  | scons _ x s =>
    debug (print_endline (show x));;
    match s tt with
    | snil _ => ret x
    | scons _ x' s =>
      debug (print_endline (show x'));;
      error "Solution is not unique"
    end
  end.

Definition main : m unit :=
  p <- deduce_assignments;;
  debug (print_endline (show_assignments p));;
  code <- check_unique show_code (enum p);;
  let oto := opcode_to_op code in
  ' (Regs r0 _ _ _) <- fold_read (interp_instr oto) (Regs 0 0 0 0);;
  print r0.

End main.

Import SimpleIO.

Parameter parse_sample : forall {regs instr},
    (int -> int -> int -> int -> regs) ->
    (int -> int -> int -> int -> instr) ->
    IO (option (sample_ regs instr)).
Extract Constant parse_sample => "
  fun regs instr k ->
    k (try
      Scanf.scanf
        ""Before: [%d, %d, %d, %d] %d %d %d %d After: [%d, %d, %d, %d] ""
        (fun r0 r1 r2 r3 o a b c s0 s1 s2 s3 ->
          Some ((regs r0 r1 r2 r3, instr o a b c), regs s0 s1 s2 s3))
       with Scanf.Scan_failure _ | End_of_file -> None)".

Definition read_sample : IO (option sample) :=
  let z := z_of_int in
  let Regs' r0 r1 r2 r3 := Regs (z r0) (z r1) (z r2) (z r3) in
  let Instr' o a b c := Instr (z o) (z a) (z b) (z c) in
  parse_sample Regs' Instr'.

Local Instance MonadI_sample_IO : MonadI sample IO :=
  read_sample.

Parameter parse_instr : forall {instr},
    (int -> int -> int -> int -> instr) ->
    IO (option instr).
Extract Constant parse_instr => "
  fun instr k ->
    k (try Scanf.scanf ""%d %d %d %d ""
             (fun o a b c -> Some (instr o a b c))
       with End_of_file -> None)".

Definition read_instr : IO (option instr) :=
  let z := z_of_int in
  let Instr' o a b c := Instr (z o) (z a) (z b) (z c) in
  parse_instr Instr'.

Local Instance MonadI_instr_IO : MonadI instr IO :=
  read_instr.

Definition exe : io_unit := IO.unsafe_run main.
Extraction "day16_2.ml" exe.
