(* ***************************************************************** *)
(* Properties.v                                                      *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)

(* ################################################################# *)
(** * Extended Validation *)
(** In order to state and prove soundness precisely, the typing rules
    must be extended to the dynamic components of the abstract runtime,
    that is, the store, configurations, and administrative instructions
 *)

From Wasm Require Import Validation.
From Wasm Require Import Execution.

(* ----------------------------------------------------------------- *)
(** *** Values and Results *)

Reserved Notation " '⊢v' v ∈ t" (at level 70).
Inductive valid_value : instr -> valtype -> Prop :=

  | VV : forall c t,
      t = type_of c ->
      ⊢v (Const c) ∈ t

where " '⊢v' v ∈ t" := (valid_value v t).


Reserved Notation " '⊢r' r ∈ ts" (at level 70).
Inductive valid_result : result -> list valtype -> Prop :=

  | VR_val : forall vals ts,
      (* Coercion doesn't work here, have to manually lift *)
      Forall2 (fun val t => ⊢v (Const val) ∈ t) vals ts ->
      ⊢r R_val vals ∈ ts

  | VR_trap : forall ts,
      ⊢r R_trap ∈ ts

where " '⊢r' r ∈ ts" := (valid_result r ts).

(* ----------------------------------------------------------------- *)
(** *** Alternative Def of Val as Proof-Carry Instr *)

(*
Reserved Notation " 'isval' v " (at level 70).
Inductive is_val : instr -> Prop :=

  | Val : forall c,
      isval (Const c)

where " 'isval' v " := (is_val v).

Record value :=
  {
    v : instr;
    H : isval v;
  }. 

Example v1 :=
  {|
    v := Const (i32 I32.zero);
    H := Val (i32 I32.zero);
  |}.

Compute v1.(H).

(* Problem on getting c to compare with I32.zero *)
Fail Definition get_c (i: value) : val :=
  match i.(H) with
    | Val c => c
  end.

*)
  

(* ----------------------------------------------------------------- *)
(** *** Store Validity *)


(* ----------------------------------------------------------------- *)
(** *** Configuration Validity *)


(* ----------------------------------------------------------------- *)
(** *** Administrative Instructions *)


(* ----------------------------------------------------------------- *)
(** *** Store Extension *)