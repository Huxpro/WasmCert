(* ***************************************************************** *)
(* Progress.v                                                        *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)

(* ################################################################# *)
(** * Progress *)

From Wasm Require Export Validation.
From Wasm Require Export Execution.
From Wasm Require Export ExtendedValidation.

Theorem progress : forall S T rt,
    ⊢c (S, T) ∈ rt ->
    (* missing Prop to claim instrs are result
       so we only write take a step here.
     *)
    exists S' T', $(S, T) ↪ $(S', T').
Proof.
  Abort.
