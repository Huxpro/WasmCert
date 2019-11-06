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

(* TODO: Extract the common lemma *)
From Wasm Require Export Preservation.

(* Coercions are too confusing during proofs. *)
Set Printing Coercions.

(* Sometimes. *)
(* Unset Printing Notations. *)

(**************************************************************)
(** ** Implicit Types - Copied from ExtendedTyping *)

(* Primary *)
Implicit Type b : bool.
Implicit Type n m : nat.

(* Value *)
Implicit Type val : val.
Implicit Type vals : list val.

(* Structure *)
Implicit Type M : module.
Implicit Type l : labelidx.

Implicit Type instr : instr.
Implicit Type instrs : list instr.
Implicit Type f func : func.
Implicit Type fs funcs : list func.
Implicit Type tab table: table.
Implicit Type tabs tables: list table.

(* Type *)
Implicit Type t : valtype.
Implicit Type ts : list valtype.
Implicit Type rt : resulttype.
Implicit Type bt : blocktype.
Implicit Type ft functype: functype.
Implicit Type fts functypes: list functype.
Implicit Type tt tabletype: tabletype.
Implicit Type tts tabletypes: list tabletype.

(* Validation *)
Implicit Type C : context.

(* Execution *)
Implicit Type cfg : config.
Implicit Type res : result.
Implicit Type S : store.
Implicit Type F : frame.
Implicit Type T : thread.
Implicit Type E : eval_context.

Implicit Type ainstr : admin_instr.
Implicit Type ainstrs : list admin_instr.

Implicit Type fa: funcaddr.
Implicit Type fas : list funcaddr.
Implicit Type ta: tableaddr.
Implicit Type tas : list tableaddr.

Implicit Type fi funcinst: funcinst.
Implicit Type fis funcinsts: list funcinst.
Implicit Type ti tableinst: tableinst.
Implicit Type tis tableinsts: list tableinst.

Implicit Type Mi mi moduleinst: moduleinst.


(* ================================================================= *)
(** ** Termination State *)
(** Terminal thread/config was not explicit defined. Should be straightforward.

    Q1:
      How to construct a result during step relation?
    A:
      we need to extract [list val] or [Trap] from [list admin_instr]
      to be able to construct [result] then construct [valid_result]. 

    Q2:
      [Inductive result] looks redundant,
      like [val], it's coincident with [instr]/[admin_instr].
      It's not used in other places besides of [valid_result]
    A:
      one important fact about [Inductive result] is that,
      like [val], it contains more information than [instr].\
      It's equiv to a proof-carrying form of [instr].
 *)

(* Transform between [result] and [admin_instr] *)


Definition result_to_ainstr (res: result) : list admin_instr :=
  match res with
  | R_vals vals => ⇈vals  (* lost information *)
  | R_trap => [Trap]
  end.

Notation "! res" := (result_to_ainstr res) (at level 9).

Example ex : list admin_instr := !R_trap.
  

(* extended from [valid_result] *)
Reserved Notation " '⊢R' T '∈' rt" (at level 70).
Inductive result_thread : thread -> resulttype -> Prop :=

  | RT : forall res rt F,
      ⊢r res ∈ rt ->
      ⊢R (F, !res) ∈ rt

where " '⊢R' T '∈' rt" := (result_thread T rt).
Hint Constructors result_thread.

Lemma R_vals_ϵ :
    !(R_vals []) = @nil admin_instr.
Proof.
  auto.
Qed.

Lemma F_ϵ_R: forall F,
    ⊢R (F, []) ∈ [].
Proof.
  intros.
  rewrite <- R_vals_ϵ.
  econstructor.
  econstructor.
  econstructor.
Qed.

Lemma F_Trap_R: forall F rt,
    ⊢R (F, [Trap]) ∈ rt.
Proof.
  intros.
  asserts_rewrite ([Trap] = !R_trap). reflexivity.
  econstructor.
  econstructor.
Qed.

(* ================================================================= *)
(** ** Progress - VAIS_snoc -> SC_simple*)


(* ================================================================= *)
(** ** Main Theorem *)

Theorem progress : forall S T rt,
    ⊢c (S, T) ∈ rt ->
    ⊢R T ∈ rt \/ exists S' F' ainstrs', $(S, T) ↪ (S', F', ainstrs').   (* [exists T'] is harder *)
Proof with eauto.
  introv HVC.

  (* valid_config *)
  inverts HVC as HSok HVT.
    (* valid_store *)
    (* valid_thread *)
    inverts HVT as HVA HVAIS.
      (* valid_frame *)
      inverts HVA as HVMI HVV.
        (* valid_moduleinst *)
        (* valid_value *)
      (* valid_admin_instrs *)

  dependent induction HVAIS.

  - (* VAIS_empty *)
    left.
    apply F_ϵ_R.

  - remember {| A_locals := vals; A_module := mi |} as F.
    remember (C0 with_locals = ts with_return = None) as C.
    rename H into HVAI__N.
    (* VAIS_snoc:

      [IHHVAIS : ... ->
      [          ⊢R (F, ainstrs) ∈ rt 
      [          \/ exists S' T', (S0, F, ainstrs) ↪ $(S', T')

      [HVAIS : (S,C) ⊢a* ainstrs ∈ ϵ --> (ts0 ++ ts2)]
      [HVAI__N : (S,C) ⊢a  ainstr__N ∈ ts2 --> ts3]             (* H *)
     --------------------------------------------------------------
       ⊢R (F, ainstrs ++ [ainstr__N])
      [  \/ exists S' T', (S, F, ainstrs ++ [ainstr__N]) ↪ $(S', T') ]
    *)
    inverts HVAI__N as.
  
    + (* VAI_instr *)
      intros HVI__N.
      inverts keep HVI__N.

      ++ (* VI_const *)
        (* we have shown [ainstrs ++ ⇈[val]] is a normal form
          but how do we show it's a result of vals?
          i.e. all ainstrs here should be some [vals] as well? *)
        admit.

      ++ (* VI_unop *)
        edestruct IHHVAIS as [HRT | HS]; try solve [subst; eauto].
        +++ (* ⊢R *) 
          (* TODO: extracting lemma *)
          inverts HRT as HVR.
          inverts HVR as HForall2.
          ++++ (* VR_vals *)
            right.

(* A stronger version of [Forall2_app_inv_r] *)
Lemma Forall2_snoc_app_r: forall {X Y : Type} {R: X -> Y -> Prop} (xs: list X) (ys': list Y) (y: Y),
     Forall2 R xs (ys' ++ [y]) ->
     exists xs' x, Forall2 R xs' ys' /\ R x y /\ xs = xs' ++ [x].
Proof.
  introv HForall2.
  apply Forall2_app_inv_r in HForall2.
  destruct HForall2 as (xs' & unit & Hxs' & Hunit & Heq).
  inverts Hunit as HRxy Hnil.
  inverts Hnil.
  exists xs' x.
  splits; auto.
Qed.

         
            apply Forall2_snoc_app_r in HForall2.
            destruct HForall2 as (vals' & val & Hvals' & Hval & Heqvals0).
            rewrite Heqvals0. simpl in *.
            rewrite upup_app. simpl in *.
            rewrite <- app_assoc. simpl.

Lemma recover_E_seq: forall vals ainstrs, 
    ⇈vals ++ ainstrs = plug__E (E_seq vals E_hole []) ainstrs.
Proof.
  intros. 
  simpl in *. 
  rewrite app_nil_r.
  auto.
Qed.

            rewrite recover_E_seq. 
            remember (E_seq vals' E_hole []) as E.
            exists S F. 
            destruct (eval_unop op val) eqn:Heval.
            +++++ 
              destruct x;
              eexists;
                eapply SC_E;
                eapply SC_simple.
              ++++++ (* Ok Some *)
                eapply SS_unop__some...
                
              ++++++ (* Ok None *)
                eapply SS_unop__none...

            +++++ (* Err *)
              inverts Hval as Heqtype_of.

(* TODO: prove in Numerics.v *)
Lemma eval_unop_no_runtime_err: forall op val,
     type_of op = type_of val ->
     eval_unop op val = Err ->
     False.
Proof.
  introv Heq.
  unfold not. intro Heval.
  unfold eval_unop in *.
  (* destruct op; destruct val; simpl in *; *)
  (*   (* good cases *) *)
  (*   try reflexivity; *)
  (*   (* bad cases *) *)
  (*     destruct u. *)
Admitted.

            destruct (eval_unop_no_runtime_err op val Heqtype_of Heval).
  


          ++++ (* VR_trap *)
            right. simpl.
            asserts_rewrite (
                [Trap; Plain (Unop op)] = [Trap] ++ [Plain (Unop op)]
              ). reflexivity.

Lemma recover_app_E_seq: forall ainstrs ainstrs', 
    ainstrs ++ ainstrs' = plug__E (E_seq [] E_hole ainstrs') ainstrs.
Proof with auto.
  intros. 
  simpl in *...
Qed.
            rewrite recover_app_E_seq.
            exists S F [Trap].
            apply SC_trap__E.

        +++ (* ↪ *)
          (* TODO: extract as a common case *)
          right.
          rewrite recover_app_E_seq.
          remember (E_seq [] E_hole [Plain (Unop op)]) as E.
          destruct HS as (S' & F' & ainstrs' & HSC).
          exists S' F' (plug__E E ainstrs').
          eapply SC_E.
          apply HSC.

      ++ (* VI_binop *)
Abort.        



(** Archive *)

(* For SC_Simple, we don't care S and F *)
Lemma progress_SC_simple : forall S C F ainstrs ainstr__N ts0 ts2 ts3,
      (S,C) ⊢a* ainstrs ∈ [] --> (ts0 ++ ts2) ->  (* [HVAIS] *)  
      (S,C) ⊢a  ainstr__N ∈ ts2 --> ts3 ->          (* [HVAI__N] *)
(* -------------------------------------------------------------- *)
      ⊢R (F, ainstrs ++ [ainstr__N]) ∈ ts0 ++ ts3
      \/ exists S' T', (S, F, ainstrs ++ [ainstr__N]) ↪ $(S', T').
Proof with eauto.
  introv HVAIS HVAI__N.
  inverts HVAI__N as.
  
  - (* VAI_instr *)
    intros HVI__N.
    inverts keep HVI__N.

    + (* VI_const *)
      left.
      (* we have shown [ainstrs ++ ⇈[val]] is a normal form
         but how do we show it's a result of vals?
         i.e. all ainstrs here should be some [vals] as well? *)
      admit.

    + (* VI_unop *)
      right.
      (*

  HVAIS : (S, C) ⊢a* ainstrs ∈ [] --> (ts0 ++ [type_of op])
--------------------------------------------------------------
 [exists S' T', (S, F, ainstrs ++ [Plain (Unop op)]) ↪ $ (S', T')]

The problem here is that,
the substructure [ainstrs] could take a step...
when it's not, it would be a result
- either it's trap, then we trap
- or it's a value, then we can possibly take a step

meaning we need a induction hypothesis on HVAIS here.
       *)
Abort.



  
