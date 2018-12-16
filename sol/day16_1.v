From Coq Require Import
     String List Arith ZArith.
Import ListNotations.

From ExtLib.Structures Require Import
     Monad MonadFix.

From SimpleIO Require RawChar.

From advent Require Import lib sol.day16_common.

Module Import DB.
Import RawChar.
(* TODO send to simple-io. *)
Definition debug_switch := false. (* Switch this to [true] for debug
                                     output. *)
Parameter debug' : forall {A}, ocaml_string -> ocaml_string -> A -> A.
Extract Constant debug' => "fun s n x -> Printf.printf ""%s: %s\n"" s n; x".
Definition debug : forall {A}, string -> string -> A -> A :=
  fun _ s n =>
    if debug_switch then debug' (to_ostring s) (to_ostring s)
    else fun x => x.
End DB.

Section main.

Import MonadNotation.
Local Open Scope monad_scope. 

Definition sample_ (regs : Type) : Type :=
  regs * Z * Z * Z * regs.

Definition sample : Type := sample_ regs.

Context {m : Type -> Type} `{Monad m} `{MonadFix m}
        `{FoldRead sample m} `{MonadO N m}.

Definition plausibles : sample -> list op :=
  fun '(rs, a, b, c, rs') =>
    filter
      (fun o =>
         let b := eqb_reg (interp (o, a, b, c) rs) rs' in
         debug (if b then "Y" else "N") (show_op o) b
      )
      all_ops.

Definition count_3plausibles : m N :=
  fold_read
    (fun n s =>
      if 3 <=? length (plausibles s) then (1 + n)%N else n%N
    ) 0%N.

Definition main : m unit := (count_3plausibles >>= print).

End main.

Import RawChar.

Parameter parse_sample : forall {regs},
    (int -> int -> int -> int -> regs) ->
    (int -> Z) ->
    IO (option (sample_ regs)).
Extract Constant parse_sample => "
  fun regs z k ->
    k (try
      Scanf.scanf
        ""Before: [%d, %d, %d, %d] %_d %d %d %d After: [%d, %d, %d, %d] ""
        (fun r0 r1 r2 r3 a b c s0 s1 s2 s3 ->
          Some ((((regs r0 r1 r2 r3, z a), z b), z c), regs s0 s1 s2 s3))     with Scanf.Scan_failure _ | End_of_file -> None
    )".

Definition read_sample : IO (option sample) :=
  let z := z_of_int in
  let Regs' r0 r1 r2 r3 := Regs (z r0) (z r1) (z r2) (z r3) in
  parse_sample Regs' z.

Local Instance MonadI_sample_IO : MonadI sample IO :=
  read_sample.

Definition exe : io_unit := IO.unsafe_run main.
Extraction "day16_1.ml" exe.
