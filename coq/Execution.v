
(* ***************************************************************** *)
(* Execution.v                                                       *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)


(* ################################################################# *)
(** * Execution *)

From Wasm Require Export Structure.



(* ================================================================= *)
(** ** Runtime Structure *)
(** http://webassembly.github.io/spec/core/exec/runtime.html *)


(* ----------------------------------------------------------------- *)
(** *** Values *)

Inductive val :=
  | const_i32 : i32 -> val
  | const_i64 : i64 -> val
  | const_f32 : f32 -> val
  | const_f64 : f64 -> val.


(* ----------------------------------------------------------------- *)
(** *** Results *)

Inductive result :=
  | R_val: list val
  | R_trap.


(* ----------------------------------------------------------------- *)
(** *** Stack *)


(** **** Activations and Frames *)


(* ----------------------------------------------------------------- *)
(** *** Administrative Instructions *)

Inductive instr :=
  | E_instr (_ : Structure.instr)
  | E_trap
  | E_label : nat -> list instr -> list instr -> instr
  | E_frame : nat -> list frame -> list instr -> instr
