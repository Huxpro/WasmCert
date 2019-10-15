(* ***************************************************************** *)
(* Values.v                                                          *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)


(* ################################################################# *)
(** * Values  *)

From Wasm Require Export Int.
From Wasm Require Export Float.
From Wasm Require Export Types.


(* ================================================================= *)
(** ** Structure - Value *)

(** Definied in [Int.v] and [Float.v] *)

Module ValRepTest.

  Definition should_be_32 := I32.bitwidth.

End ValRepTest.


(* ----------------------------------------------------------------- *)
(** *** Bytes *)

Parameter byte : Type.


(* ================================================================= *)
(** ** Execution - Runtime Structure - Values *)

(** From the reference interpter...
    Module and constructors use different namespace:

        type ('i32, 'i64, 'f32, 'f64) op =
          I32 of 'i32 | I64 of 'i64 | F32 of 'f32 | F64 of 'f64

        type value = (I32.t, I64.t, F32.t, F64.t) op

    But here in Coq we can start constructor name in lowercase anyway.
 *)


(* op is a sum that representing any 4-ways things *)

Inductive op (i32 i64 f32 f64 : Type) :=
  | i32 (_: i32)
  | i64 (_: i64)
  | f32 (_: f32)
  | f64 (_: f64).
Arguments i32 {i32} {i64} {f32} {f64} _.
Arguments i64 {i32} {i64} {f32} {f64} _.
Arguments f32 {i32} {i64} {f32} {f64} _.
Arguments f64 {i32} {i64} {f32} {f64} _.


(* wasm vals is sum of 4 concrete rep value. *)

Definition val := op I32.t I64.t F32.t F64.t.


(* functor map ops to wasm types. *)

Definition type_of {i32 i64 f32 f64 : Type} (ops : op i32 i64 f32 f64) : valtype :=
  match ops with
  | i32 _ => T_i32
  | i64 _ => T_i64
  | f32 _ => T_f32
  | f64 _ => T_f64
  end.


(* map [valtype*] to corresponding zeros *)

Definition zeros (ts: list valtype) : list val :=
  map (fun t => match t with
           | T_i32 => i32 I32.zero
           | T_i64 => i64 I64.zero
           | T_f32 => f32 F32.zero
           | T_f64 => f64 F64.zero
         end) ts.


(* functor map ops to concrete rep's coq type. *)

Definition rep_type_of {i32 i64 f32 f64 : Type} (ops : op i32 i64 f32 f64) : Type :=
  match ops with
  | i32 _ => I32.t
  | i64 _ => I64.t
  | f32 _ => F32.t
  | f64 _ => F64.t
  end.


(* bool is represented as i32 *)

Definition bool_to_i32 (b : bool) : val :=
  match b with
  | true => i32 I32.one
  | false => i32 I32.zero
  end.
Coercion bool_to_i32 : bool >-> val.


(* nat is used to index vector *)

Definition nat_to_i32 (n : nat) : val :=
  match n with
  | 0 => i32 I32.zero
  | n => i32 (I32.from_nat n)
  end.
Coercion nat_to_i32 : nat >-> val.


Module ValTest.

  Parameter c32 : I32.t.
  Definition c64 := I64.zero.

  Example v1: val := i32 c32.
  Example e1: rep_type_of v1 = I32.t. auto. Qed.

  Example v2 : val := i64 (I64.zero).

  Example vb: val := true.

  Fail Example v3 := I32 c64.

End ValTest.



(* ================================================================= *)
(** ** Injection & Projection *)

(** the reference interpreter simly raise exception here but here we have to make the conversion exception explicit. *)

Module Type ValType.
  Parameter t : Type.
  Parameter to_val : t -> val.
  Parameter of_val : val -> option t.
End ValType.


Module IVal32.
  Definition t := I32.t.
  Definition to_val i : val := i32 i.
  Definition of_val (v: val) :=
    match v with
    | i32 i => Some i
    | _ => None
    end.
End IVal32.


Module IVal64.
  Definition t := I64.t.
  Definition to_val i : val := i64 i.
  Definition of_val (v: val) :=
    match v with
    | i64 i => Some i
    | _ => None
    end.
End IVal64.


Module FVal32.
  Definition t := F32.t.
  Definition to_val f : val := f32 f.
  Definition of_val (v: val) :=
    match v with
    | f32 f => Some f
    | _ => None
    end.
End FVal32.


Module FVal64.
  Definition t := F64.t.
  Definition to_val f : val := f64 f.
  Definition of_val (v: val) :=
    match v with
    | f64 f => Some f
    | _ => None
    end.
End FVal64.
