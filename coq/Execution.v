
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

(** In the current version of WebAssembly, a result can consist of at most one value. *)

Inductive result :=
  | R_val: list val -> result
  | R_trap.


(* ----------------------------------------------------------------- *)
(** *** Addresses *)

Definition addr := nat.
Notation funcaddr := addr.
Notation tableaddr := addr.
Notation memaddr := addr.
Notation globaladdr := addr.


(* ----------------------------------------------------------------- *)
(** *** Module Instances *)

Record moduleinst :=
  {
    types : list functype;
    funcaddrs : list funcaddr;
    (* tableaddrs : list tableaddr; *)
    (* memaddrs : list memaddr; *)
    (* globaladdrs : list globaladdr; *)
    (* exports : list exportinst; *)
  }.


(* ----------------------------------------------------------------- *)
(** *** Function Instances *)

(** hostfunc case is ignore for now *)

Record funcinst :=
  {
    type : functype;
    module : moduleinst;
    code : func;
  }.

(* ----------------------------------------------------------------- *)
(** *** Store *)
(** https://webassembly.github.io/multi-value/core/exec/runtime.html#store *)

Record store :=
  {
    funcs : list funcinst;
    (* tables : list tableinst; *)
    (* mems : list meminst; *)
    (* globals : list globalinst; *)
  }.


(* ----------------------------------------------------------------- *)
(** *** Stack *)


(** **** Activations and Frames *)

Record frame :=
  {
    locals: list val;
    frame_module: moduleinst;
  }.

Inductive activation :=
  | Frame (arity : nat) (_ : frame).


(* ----------------------------------------------------------------- *)
(** *** Administrative Instructions *)

Inductive instr :=
  | E_instr (_ : Structure.instr)
  | E_trap
  | E_label : nat -> list instr -> list instr -> instr
  | E_frame : nat -> list frame -> list instr -> instr.


(** **** Blocking Contexts *)


(** **** Configurations *)

Notation thread := (frame * (list instr))%type.

Definition config : Type := store * thread.


(** **** Evaluation Contexts *)





                                          