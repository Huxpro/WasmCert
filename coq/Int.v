(* ***************************************************************** *)
(* Int.v                                                             *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)


(* ################################################################# *)
(** * Int  *)

(* ----------------------------------------------------------------- *)
(** *** Value representation (placeholder) *)

(** TODO: use actual implementation such as Coq standard library's
    or Int32, Int64, Float32, Float64 from OCaml.
 *)

Module Type Rep.
  Parameter bitwidth: nat.
End Rep.

Module Rep32.
  Definition bitwidth := 32.
End Rep32.

Module Rep64.
  Definition bitwidth := 64.
End Rep64.


(* ----------------------------------------------------------------- *)
(** *** Functor *)

Module Type S.
  Parameter t : Type.
  Parameter bitwidth: nat.

  Parameter zero : t.
  Parameter one : t.
  Parameter min : t.
  Parameter max : t.
  Parameter max16 : t.

  Parameter from_nat : nat -> t.
  Parameter to_nat : t -> nat.

  (* iunop *)
  Parameter clz    : t -> option t.
  Parameter ctz    : t -> option t.
  Parameter popcnt : t -> option t.

  (* ibinop *)
  Parameter add   : t -> t -> option t.
  Parameter sub   : t -> t -> option t.
  Parameter mul   : t -> t -> option t.
  Parameter div_s : t -> t -> option t.
  Parameter div_u : t -> t -> option t.
  Parameter rem_s : t -> t -> option t.
  Parameter rem_u : t -> t -> option t.
  Parameter and   : t -> t -> option t.
  Parameter or    : t -> t -> option t.
  Parameter xor   : t -> t -> option t.
  Parameter shl   : t -> t -> option t.
  Parameter shr_s : t -> t -> option t.
  Parameter shr_u : t -> t -> option t.
  Parameter rotl  : t -> t -> option t.
  Parameter rotr  : t -> t -> option t.

  (* itestop *)
  Parameter eqz : t -> bool.

  (* iretop *)
  Parameter eq   : t -> t -> bool.
  Parameter ne   : t -> t -> bool.
  Parameter lt_s : t -> t -> bool.
  Parameter lt_u : t -> t -> bool.
  Parameter gt_s : t -> t -> bool.
  Parameter gt_u : t -> t -> bool.
  Parameter le_s : t -> t -> bool.
  Parameter le_u : t -> t -> bool.
  Parameter ge_s : t -> t -> bool.
  Parameter ge_u : t -> t -> bool.

  (* axioms *)
End S.


Module Make (R: Rep) : S.
  Include R.

  Parameter t : Type.

  Parameter zero : t.
  Parameter one : t.
  Parameter min : t.
  Parameter max : t.
  Parameter max16 : t.

  Parameter from_nat : nat -> t.
  Parameter to_nat : t -> nat.

  (* iunop *)
  Parameter clz    : t -> option t.
  Parameter ctz    : t -> option t.
  Parameter popcnt : t -> option t.

  (* ibinop *)
  Parameter add   : t -> t -> option t.
  Parameter sub   : t -> t -> option t.
  Parameter mul   : t -> t -> option t.
  Parameter div_s : t -> t -> option t.
  Parameter div_u : t -> t -> option t.
  Parameter rem_s : t -> t -> option t.
  Parameter rem_u : t -> t -> option t.
  Parameter and   : t -> t -> option t.
  Parameter or    : t -> t -> option t.
  Parameter xor   : t -> t -> option t.
  Parameter shl   : t -> t -> option t.
  Parameter shr_s : t -> t -> option t.
  Parameter shr_u : t -> t -> option t.
  Parameter rotl  : t -> t -> option t.
  Parameter rotr  : t -> t -> option t.

  (* itestop *)
  Parameter eqz : t -> bool.

  (* iretop *)
  Parameter eq   : t -> t -> bool.
  Parameter ne   : t -> t -> bool.
  Parameter lt_s : t -> t -> bool.
  Parameter lt_u : t -> t -> bool.
  Parameter gt_s : t -> t -> bool.
  Parameter gt_u : t -> t -> bool.
  Parameter le_s : t -> t -> bool.
  Parameter le_u : t -> t -> bool.
  Parameter ge_s : t -> t -> bool.
  Parameter ge_u : t -> t -> bool.

  (* axioms *)
End Make.


(* ----------------------------------------------------------------- *)
(** *** Make *)

Module I32 := Int.Make(Rep32).
Module I64 := Int.Make(Rep64).
