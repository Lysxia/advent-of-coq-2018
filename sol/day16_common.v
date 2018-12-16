From Coq Require Import
     String List Arith ZArith
     FMapAVL OrderedTypeEx.
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

Definition eqb_ri (ri1 ri2 : RI) : bool :=
  match ri1, ri2 with
  | R, R | I, I => true
  | _, _ => false
  end.

Lemma eq_eqb_ri ri1 ri2 :
  ri1 = ri2 -> eqb_ri ri1 ri2 = true.
Proof.
  destruct ri1; intros []; reflexivity.
Qed.

Definition eqb_op o1 o2 : bool :=
  match o1, o2 with
  | Add ri1, Add ri2 | Mul ri1, Mul ri2
  | Ban ri1, Ban ri2 | Bor ri1, Bor ri2
  | Set' ri1, Set' ri2 =>
    eqb_ri ri1 ri2
  | Gt riA1 riB1, Gt riA2 riB2
  | Eq riA1 riB1, Eq riA2 riB2 =>
    eqb_ri riA1 riA2 && eqb_ri riB1 riB2
  | _, _ => false
  end.

Lemma eq_eqb_op o1 o2 :
  o1 = o2 -> eqb_op o1 o2 = true.
Proof.
  destruct o1; intros []; simpl;
    repeat rewrite eq_eqb_ri; reflexivity.
Qed.

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

Instance Dummy_RI : Dummy RI.
Proof. exact R. Qed.

Instance Dummy_op : Dummy op.
Proof. exact (Add dummy). Qed.

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

Definition is_reg (a : Z) : bool :=
  ((0 <=? a) && (a <? 4))%Z.

Definition is_ri (ri : RI) (a : Z) : bool :=
  match ri with
  | R => is_reg a
  | I => true
  end.

Definition wf : instr -> bool :=
  fun '(o, a, b, _) =>
    match o with
    | Add riB | Mul riB | Ban riB
    | Bor riB => is_ri riB b
    | Set' riA => is_ri riA a
    | Gt riA riB | Eq riA riB => is_ri riA a && is_ri riB b
    end.

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
