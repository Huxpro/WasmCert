(* ***************************************************************** *)
(* Structure.v                                                       *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)


(* ################################################################# *)
(** * Structure *)

From Wasm Require Export Values.

From Wasm Require Export Types.
Export FunctypeNotations.

From Wasm Require Export Commons.
Export ListNotations.


(** Module Type, Signature.. **)
From Coq Require Export Structures.Equalities.

(* ================================================================= *)
(** ** Modules (Pre) *)


(* ----------------------------------------------------------------- *)
(** *** Indices *)

(** https://webassembly.github.io/multi-value/core/syntax/modules.html#indices *)

(** technically, indices are u32 so it's bounded.
    currently we generalized both indices and vec as unbounded.
  *)

Definition typeidx := nat.
Definition funcidx := nat.
Definition tableidx := nat.
Definition memidx := nat.
Definition globalidx := nat.
Definition localidx := nat.
Definition labelidx := nat.



(* ================================================================= *)
(** ** Values *)

(** See [Value.v] *)


(* ================================================================= *)
(** ** Types *)

(** See [Types.v] *)


(* ================================================================= *)
(** ** Instruction *)

(** nn, mm

    the set of possible rewritting result is

      {i32, i64, f32, f64}

    which is isomorphic with the valtype. so we can safely use valtype as the constraint when defining instructions.
 *)

Inductive sx :=
  | U
  | S.

Module IntOp.

  Inductive unop :=
    | Clz
    | Ctz
    | Popcnt.

  Inductive binop := 
    | Add
    | Sub
    | Mul
    | Div (_: sx)
    | Rem (_: sx)
    | And
    | Or
    | Xor
    | Shl
    | Shr (_: sx)
    | Rotl
    | Rotr.

  Inductive testop :=
    | Eqz.

  Inductive relop :=
    | Eq
    | Ne
    | Lt (_: sx)
    | Gt (_: sx)
    | Le (_: sx)
    | Ge (_: sx).

  Inductive cvtop :=
    | Wrap_i64           (* i32. *)
    | Extend_i32 (_: sx) (* i64. *)
    | Trunc_f32 (_: sx)
    | Trunc_f64 (_: sx)
    | Reinterpret.

End IntOp.

Module FloatOp.

  Inductive unop :=
    | Abs
    | Neg
    | Sqrt
    | Ceil
    | Floor
    | Trunc
    | Nearest.

  Inductive binop :=
    | Add
    | Sub
    | Mul
    | Div
    | Min
    | Max
    | Copysign.

  Inductive testop :=.

  Inductive relop :=
    | Eq
    | Ne
    | Lt
    | Gt
    | Le
    | Ge.

  Inductive cvtop :=
    | Demote_f64          (* f32. *)
    | Promote_f32         (* f64. *)
    | Convert_i32 (_: sx)
    | Convert_i64 (_: sx)
    | Reinterpret.

End FloatOp.

Module IOp32 := IntOp.
Module IOp64 := IntOp.
Module FOp32 := FloatOp.
Module FOp64 := FloatOp.

Definition unop := @op IOp32.unop IOp64.unop FOp32.unop FOp64.unop.
Definition binop := @op IOp32.binop IOp64.binop FOp32.binop FOp64.binop.
Definition testop := @op IOp32.testop IOp64.testop FOp32.testop FOp64.testop.
Definition relop := @op IOp32.relop IOp64.relop FOp32.relop FOp64.relop.
Definition cvtop := @op IOp32.cvtop IOp64.cvtop FOp32.cvtop FOp64.cvtop.


(* ----------------------------------------------------------------- *)
(** *** Control Instructions - blocktype *)

Inductive blocktype :=
  | BT_typeidx (t: typeidx)
  | BT_valtype (v: option valtype).


Inductive instr :=
(* ----------------------------------------------------------------- *)
(** *** Numeric Instruction *)
  | Const (v: val)
  | Unop (op: unop)
  | Binop (op: binop)
  | Testop (op: testop)
  | Relop (op: relop)
  (* | Cvtop (op: cvtop) *)

(* ----------------------------------------------------------------- *)
(** *** Parametric Instruction *)
  | Drop
  | Select

(* ----------------------------------------------------------------- *)
(** *** Variable Instruction *)
  | Local_get (i: localidx)
  | Local_set (i: localidx)
  | Local_tee (i: localidx)
  (* | Global_get (i: globalidx) *)
  (* | Global_set (i: globalidx) *)

(* ----------------------------------------------------------------- *)
(** *** Memory Instruction *)

(* ----------------------------------------------------------------- *)
(** *** Control Instructions *)
  | Nop
  | Unreachable
  | Block (bt: blocktype) (b: list instr)
  | Loop (bt: blocktype) (b: list instr)
  | If (bt: blocktype) (b1: list instr) (b2: list instr)
  | Br (l: labelidx)
  | Br_if (l: labelidx)
  | Br_table (ls: list labelidx) (l: labelidx)
  | Return
  | Call (f: funcidx)
  | Call_indirect (t: typeidx).

Coercion Const : val >-> instr.


Definition expr : Type := list instr.


(* ================================================================= *)
(** ** Modules (Post) *)


(* ----------------------------------------------------------------- *)
(** *** Functions *)

Record func :=
  {
    F_type : typeidx;
    F_locals : list valtype;
    F_body: expr;
  }.

(* ----------------------------------------------------------------- *)
(** *** Tables *)

Record table :=
  {
    T_type : tabletype;
  }.


(* ----------------------------------------------------------------- *)
(** *** Module *)

Record module :=
  {
    M_types  : list functype;
    M_funcs  : list func;
    M_tables : list table;
  }.

                  

