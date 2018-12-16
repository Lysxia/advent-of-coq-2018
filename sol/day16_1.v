From Coq Require Import
     String List Arith ZArith.
Import ListNotations.

From ExtLib.Structures Require Import
     Monad MonadFix.

From SimpleIO Require RawChar.

From advent Require Import lib.

Local Open Scope bool_scope.

(* Register or Immediate *)
Variant RI : Type := R | I.

Variant op : Type :=
| Add (riB : RI)
| Mul (riB : RI)
| Ban (riB : RI)
| Bor (riB : RI)
| Set' (riA : RI) (* [Set] is a Coq keyword :( *)
(* Never I I *)
| Gt (riA riB : RI)
| Eq (riA riB : RI)
.

Definition show_ri (ri : RI) : string :=
  match ri with
  | R => "r"
  | I => "i"
  end.

Definition show_op (o : op) : string :=
  match o with
  | Add ri => "add" ++ show_ri ri
  | Mul ri => "mul" ++ show_ri ri
  | Ban ri => "ban" ++ show_ri ri
  | Bor ri => "bor" ++ show_ri ri
  | Set' ri => "set" ++ show_ri ri
  | Gt ri1 ri2 => "gt" ++ show_ri ri1 ++ show_ri ri2
  | Eq ri1 ri2 => "eq" ++ show_ri ri1 ++ show_ri ri2
  end.

Definition all_ops : list op :=
  [ Add R; Add I;
    Mul R; Mul I;
    Ban R; Ban I;
    Bor R; Bor I;
    Set' R; Set' I;
    Gt I R; Gt R I; Gt R R;
    Eq I R; Eq R I; Eq R R
  ].

Definition instr : Type := op * Z * Z * Z.

Variant regs : Type :=
  Regs (r0 : Z) (r1 : Z) (r2 : Z) (r3 : Z)
.

Definition eqb_reg : regs -> regs -> bool :=
  fun '(Regs r0 r1 r2 r3) '(Regs s0 s1 s2 s3) =>
    ((r0 =? s0) && (r1 =? s1) && (r2 =? s2) && (r3 =? s3))%Z.

Instance Dummy_regs : Dummy regs.
Proof. exact (Regs 0%Z 0%Z 0%Z 0%Z). Qed.

Instance Dummy_Z : Dummy Z.
Proof. exact 0%Z. Qed.

Definition get_reg : Z -> regs -> Z :=
  fun i '(Regs r0 r1 r2 r3) =>
    match i with
    | 0%Z => r0
    | 1%Z => r1
    | 2%Z => r2
    | 3%Z => r3
    | _ => dummy
    end.

Definition set_reg : Z -> Z -> regs -> regs :=
  fun i r '(Regs r0 r1 r2 r3) =>
    match i with
    | 0%Z => Regs r r1 r2 r3
    | 1%Z => Regs r0 r r2 r3
    | 2%Z => Regs r0 r1 r r3
    | 3%Z => Regs r0 r1 r2 r
    | _ => dummy
    end.

Definition get_ri (i : RI * Z) : regs -> Z :=
  match i with
  | (R, i) => get_reg i
  | (I, i) => fun _ => i
  end.

Definition binop_ri (f : Z -> Z -> Z)
           (a b : RI * Z) (c : Z) (rs : regs) : regs :=
  set_reg c (f (get_ri a rs) (get_ri b rs)) rs.

Definition boolop {A} (f : A -> A -> bool) : A -> A -> Z :=
  fun i j => if f i j then 1%Z else 0%Z.

Definition interp : instr -> regs -> regs :=
  fun '(o, a, b, c) rs =>
    match o with
    | Add riB => binop_ri Z.add (R, a) (riB, b) c rs
    | Mul riB => binop_ri Z.mul (R, a) (riB, b) c rs
    | Ban riB => binop_ri Z.land (R, a) (riB, b) c rs
    | Bor riB => binop_ri Z.lor (R, a) (riB, b) c rs
    | Set' riA => set_reg c (get_ri (riA, a) rs) rs
    | Gt riA riB => binop_ri (boolop Z.gtb) (riA, a) (riB, b) c rs
    | Eq riA riB => binop_ri (boolop Z.eqb) (riA, a) (riB, b) c rs
    end.

Module example.

Example ex :
  interp (Add R, 2, 1, 2)%Z (Regs 3 2 1 1) = Regs 3 2 3 1.
Proof. reflexivity. Qed.

End example.

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
