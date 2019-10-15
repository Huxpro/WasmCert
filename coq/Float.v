(* ***************************************************************** *)
(* Float.v                                                           *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)


(* ################################################################# *)
(** * Float  *)

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

  (* funop *)
  Parameter abs : t -> option t.
  Parameter neg : t -> option t.
  Parameter sqrt : t -> option t.
  Parameter ceil : t -> option t.
  Parameter floor : t -> option t.
  Parameter trunc : t -> option t.
  Parameter nearest : t -> option t.

  (* fbinop *)
  Parameter add : t -> t -> option t.
  Parameter sub : t -> t -> option t.
  Parameter mul : t -> t -> option t.
  Parameter div : t -> t -> option t.
  Parameter min : t -> t -> option t.
  Parameter max : t -> t -> option t.
  Parameter copysign : t -> t -> option t.

  (* fretop *)
  Parameter eq : t -> t -> bool.
  Parameter ne : t -> t -> bool.
  Parameter lt : t -> t -> bool.
  Parameter gt : t -> t -> bool.
  Parameter le : t -> t -> bool.
  Parameter ge : t -> t -> bool.

  (* axioms *)
End S.

Module Make (R: Rep) : S.
  Include R.

  Parameter t : Type.

  Parameter zero : t.

  (* funop *)
  Parameter abs : t -> option t.
  Parameter neg : t -> option t.
  Parameter sqrt : t -> option t.
  Parameter ceil : t -> option t.
  Parameter floor : t -> option t.
  Parameter trunc : t -> option t.
  Parameter nearest : t -> option t.

  (* fbinop *)
  Parameter add : t -> t -> option t.
  Parameter sub : t -> t -> option t.
  Parameter mul : t -> t -> option t.
  Parameter div : t -> t -> option t.
  Parameter min : t -> t -> option t.
  Parameter max : t -> t -> option t.
  Parameter copysign : t -> t -> option t.

  (* fretop *)
  Parameter eq : t -> t -> bool.
  Parameter ne : t -> t -> bool.
  Parameter lt : t -> t -> bool.
  Parameter gt : t -> t -> bool.
  Parameter le : t -> t -> bool.
  Parameter ge : t -> t -> bool.

  (* axioms *)
End Make.


(* ----------------------------------------------------------------- *)
(** *** Make *)

Module F32 := Float.Make(Rep32).
Module F64 := Float.Make(Rep64).
