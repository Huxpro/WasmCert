(* ***************************************************************** *)
(* Soundness.v                                                       *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)

(* ################################################################# *)
(** * Soundness *)
(** https://webassembly.github.io/multi-value/core/appendix/properties.html

    Type soundness of the formalized subset: a valid configuration
    never gets stuck. Every configuration it reduces to is still valid
    (preservation), and is either a result or can take another step
    (progress).
 *)

From Wasm Require Export Preservation.
From Wasm Require Export Progress.


(* ================================================================= *)
(** ** Results are Terminal *)

Lemma result_is_normal_form : forall S F ainstrs rt,
    ⊢R (F, ainstrs) ∈ rt ->
    normal_form step (S, F, ainstrs).
Proof.
  introv HR.
  inverts HR as Hres.
  destruct res; simpl.
  - apply S_F_vals_is_normal_form.
  - apply S_F_trap_is_normal_form.
Qed.


(* ================================================================= *)
(** ** Soundness *)

Theorem soundness : forall S T S' T' rt,
    ⊢c (S, T) ∈ rt ->
    ($(S, T)) ↪* ($(S', T')) ->
    ⊢c (S', T') ∈ rt /\
    (⊢R T' ∈ rt \/ exists S'' F'' ainstrs'', $(S', T') ↪ (S'', F'', ainstrs'')).
Proof.
  introv HVC Hmulti.
  destruct T as [F ainstrs], T' as [F' ainstrs']. simpl in Hmulti.
  remember (S, F, ainstrs) as cfg.
  remember (S', F', ainstrs') as cfg'.
  gen S F ainstrs.
  induction Hmulti as [cfg | cfg cfg1 cfg' HSC Hmulti IH]; intros; subst.
  - inverts Heqcfg.
    split; auto.
    apply progress. assumption.
  - destruct cfg1 as [[S1 F1] ainstrs1].
    destruct (preservation__toplevel S (F, ainstrs) S1 (F1, ainstrs1) rt HVC HSC)
      as [HVC1 _].
    eapply IH; eauto.
Qed.

(* A configuration is stuck if it is neither a result nor able to step. *)
Definition stuck (S: store) (T: thread) (rt: resulttype) : Prop :=
  ~ ⊢R T ∈ rt /\ normal_form step ($(S, T)).

Corollary type_safety : forall S T S' T' rt,
    ⊢c (S, T) ∈ rt ->
    ($(S, T)) ↪* ($(S', T')) ->
    ~ stuck S' T' rt.
Proof.
  introv HVC Hmulti [Hnot_result Hnormal].
  destruct (soundness _ _ _ _ _ HVC Hmulti) as [_ [Hresult | (S'' & F'' & ainstrs'' & HSC)]].
  - contradiction.
  - apply Hnormal. eauto.
Qed.
