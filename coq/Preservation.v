(* ***************************************************************** *)
(* Preservation.v                                                    *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)

(* ################################################################# *)
(** * Preservation *)

From Wasm Require Export Validation.
From Wasm Require Export Execution.
From Wasm Require Export ExtendedValidation.

Theorem preservation : forall S T S' T' rt,
    ⊢c (S, T) ∈ rt ->
    $(S, T) ↪ $(S', T') ->
    ⊢c (S', T') ∈ rt /\ ⊢S S ⪯ S'.
Proof.
  Abort.

