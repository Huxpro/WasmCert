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
From Wasm Require Export ProofAux.

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

Lemma R_vals_vals : forall vals,
    !(R_vals vals) = ⇈vals.
Proof.
  auto.
Qed.

Lemma F_vals_R: forall F vals rt,
    Forall2 (fun (val : val) (t : valtype) => ⊢v val ∈ t) vals rt ->
    ⊢R (F, ⇈vals) ∈ rt.
Proof with eauto.
  introv HForall2.
  rewrite <- R_vals_vals...
  econstructor.
  econstructor...
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
(** ** Lemma Forall2 *)

(* A specialized version of [Forall2_app_inv_r] *)
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

Lemma Forall2_snoc_app_r2: forall {X Y : Type} {R: X -> Y -> Prop} (xs: list X) (ys': list Y) (y1 y2: Y),
     Forall2 R xs (ys' ++ [y1; y2]) ->
     exists xs' x1 x2, Forall2 R xs' ys' /\ R x1 y1 /\ R x2 y2 /\ xs = xs' ++ [x1; x2].
Proof with eauto.
  introv HForall2.
  apply Forall2_app_inv_r in HForall2.
  destruct HForall2 as (l & r & Hl & Hr & Heq).
  inverts Hr as Hr1 Hr'.
  inverts Hr' as Hr2 Hr''.
  inverts Hr''.
  exists l x x0. splits...
Qed.

Lemma Forall2_snoc_app_r3: forall {X Y : Type} {R: X -> Y -> Prop} (xs: list X) (ys': list Y) (y1 y2 y3: Y),
     Forall2 R xs (ys' ++ [y1; y2; y3]) ->
     exists xs' x1 x2 x3, Forall2 R xs' ys' /\ R x1 y1 /\ R x2 y2 /\ R x3 y3 /\ xs = xs' ++ [x1; x2; x3].
Proof with eauto.
  introv HForall2.
  apply Forall2_app_inv_r in HForall2.
  destruct HForall2 as (l & r & Hl & Hr & Heq).
  inverts Hr as Hr1 Hr'.
  inverts Hr' as Hr2 Hr''.
  inverts Hr'' as Hr3 Hr'''.
  inverts Hr'''.
  exists l x x0 x1. splits...
Qed.


Ltac invert_Forall2_app_r1 HForall2 l r Hl Hr:=
  apply Forall2_snoc_app_r in HForall2;
  destruct HForall2 as (l & r & Hl & Hr & _Heq);
  rewrite _Heq.

Ltac invert_Forall2_app_r2 HForall2 xs' x1 x2 Hxs' Hx1 Hx2:=
  apply Forall2_snoc_app_r2 in HForall2;
  destruct HForall2 as (xs' & x1 & x2 & Hxs' & Hx1 & Hx2 & _Heq);
  rewrite _Heq.

Ltac invert_Forall2_app_r3 HForall2 xs' x1 x2 x3 Hxs' Hx1 Hx2 Hx3:=
  apply Forall2_snoc_app_r3 in HForall2;
  destruct HForall2 as (xs' & x1 & x2 & x3 & Hxs' & Hx1 & Hx2 & Hx3 & _Heq);
  rewrite _Heq.



(* ================================================================= *)
(** ** Build/Extract/Decompose Execution Context *)

(* Decompose on left, which has to be value *)
Lemma decompose_vals_as_E_seq: forall vals ainstrs, 
    ⇈vals ++ ainstrs = plug__E (E_seq vals E_hole []) ainstrs.
Proof.
  intros. 
  simpl in *. 
  rewrite app_nil_r.
  auto.
Qed.
         
Ltac decompose_vals_as_E_seq_E vals :=
  rewrite decompose_vals_as_E_seq;
  remember (E_seq vals E_hole []) as E.

(* Decompose on right, which has to be rest of the ainstrs *)
Lemma decompose_rest_as_E_seq: forall ainstrs ainstrs', 
    ainstrs ++ ainstrs' = plug__E (E_seq [] E_hole ainstrs') ainstrs.
Proof with auto.
  intros. 
  simpl in *...
Qed.

Ltac decompose_rest_as_E_seq_E rest :=
  rewrite decompose_rest_as_E_seq;
  remember (E_seq [] E_hole rest) as E.



(* ================================================================= *)
(** ** Progress - VAIS_snoc -> SC_simple*)

Ltac step_VR_trap S F list car :=
  right;
  asserts_rewrite (
    list = [Trap] ++ car
  ); try reflexivity;
  rewrite decompose_rest_as_E_seq;
  exists S F [Trap]; apply SC_trap__E.

Ltac step_snoc_app_cdr S F HSC rest :=
  right;
  decompose_rest_as_E_seq_E rest;
  destruct HSC as (S' & F' & ainstrs' & HSC);
  exists S' F'; eexists;
  eapply SC_E;
  apply HSC.


(* ================================================================= *)
(** ** Main Theorem *)

Theorem progress : forall S T rt,
    ⊢c (S, T) ∈ rt ->
    ⊢R T ∈ rt \/ exists S' F' ainstrs', $(S, T) ↪ (S', F', ainstrs').   (* TODO: [exists T'] *)
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
       we could not extract this case as a lemma since we need IH.

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
        edestruct IHHVAIS as [HRT | HSC]; try solve [subst; eauto].
        +++ (* ⊢R *) 
          inverts HRT as HVR.
          inverts HVR as HForall2; simpl.
          ++++ (* VR_vals *)
            left.
            asserts_rewrite ([Plain (Const val)] = ⇈[val]). reflexivity.
            rewrite <- upup_app.
            eapply F_vals_R.
            apply Forall2_app.
            +++++ rewrite app_nil_r in HForall2...
            +++++ constructor; try constructor...
          ++++ (* VR_trap *)
            step_VR_trap S F [Trap; Plain (Const val)] [Plain (Const val)].
        +++ (* ↪ *)
          step_snoc_app_cdr S' F' HSC [Plain (Const val)].
            

      ++ (* VI_unop *)
        edestruct IHHVAIS as [HRT | HSC]; try solve [subst; eauto].
        +++ (* ⊢R *) 
          inverts HRT as HVR.
          inverts HVR as HForall2; simpl.
          ++++ (* VR_vals *)
            right.
            invert_Forall2_app_r1 HForall2 vals' val0 Hval' Hval0.
            rewrite upup_app; rewrite <- app_assoc; simpl.
            decompose_vals_as_E_seq_E vals'.
            exists S F.
            destruct (eval_unop op val0) as [val__opt | ] eqn:Heval.
            +++++ (* Ok *)
              destruct val__opt;
              eexists;
                eapply SC_E;
                eapply SC_simple.
              ++++++ (* Ok Some *) eapply SS_unop__some...
              ++++++ (* Ok None *) eapply SS_unop__none...
            +++++ (* Err *)
              inverts Hval0 as Heqtype_of.
              destruct (eval_unop_no_runtime_err op val0 Heqtype_of Heval).
          ++++ (* VR_trap *)
            step_VR_trap S F [Trap; Plain (Unop op)] [Plain (Unop op)].
        +++ (* ↪ *)
          step_snoc_app_cdr S' F' HSC [Plain (Unop op)].


      ++ (* VI_binop *)
        edestruct IHHVAIS as [HRT | HSC]; try solve [subst; eauto].
        +++ (* ⊢R *) 
          inverts HRT as HVR.
          inverts HVR as HForall2; simpl.
          ++++ (* VR_vals *)
            right.
            invert_Forall2_app_r2 HForall2 vals' val1 val2 Hval' Hval1 Hval2.
            rewrite upup_app; rewrite <- app_assoc; simpl.
            decompose_vals_as_E_seq_E vals'.
            exists S F. 
            destruct (eval_binop op val1 val2) as [val__opt | ] eqn:Heval.
            +++++ (* Ok *)
              destruct val__opt;
              eexists;
                eapply SC_E;
                eapply SC_simple.
              ++++++ (* Ok Some *) eapply SS_binop__some...
              ++++++ (* Ok None *) eapply SS_binop__none...
            +++++ (* Err *)
              inverts Hval1 as Heqtype_of1.
              inverts Hval2 as Heqtype_of2.
              destruct (eval_binop_no_runtime_err op val1 val2 Heqtype_of1 Heqtype_of2 Heval).
          ++++ (* VR_trap *)
            step_VR_trap S F [Trap; Plain (Binop op)] [Plain (Binop op)].
        +++ (* ↪ *)
          step_snoc_app_cdr S' F' HSC [Plain (Binop op)].


      ++ (* VI_testop *)
        edestruct IHHVAIS as [HRT | HSC]; try solve [subst; eauto].
        +++ (* ⊢R *) 
          inverts HRT as HVR.
          inverts HVR as HForall2; simpl.
          ++++ (* VR_vals *)
            right.
            invert_Forall2_app_r1 HForall2 vals' val0 Hvals' Hval0.
            rewrite upup_app; rewrite <- app_assoc; simpl.
            decompose_vals_as_E_seq_E vals'.
            exists S F. 
            destruct (eval_testop op val0) as [ bval | ] eqn:Heval.
            +++++ (* Ok *)
              eexists;
                eapply SC_E;
                eapply SC_simple;
                eapply SS_testop...
            +++++ (* Err *)
              inverts Hval0 as Heqtype_of.
              destruct (eval_testop_no_runtime_err op val0 Heqtype_of Heval).
          ++++ (* VR_trap *)
            step_VR_trap S F [Trap; Plain (Testop op)] [Plain (Testop op)].
        +++ (* ↪ *)
          step_snoc_app_cdr S' F' HSC [Plain (Testop op)].


      ++ (* VI_relop *)
        edestruct IHHVAIS as [HRT | HSC]; try solve [subst; eauto].
        +++ (* ⊢R *) 
          inverts HRT as HVR.
          inverts HVR as HForall2; simpl.
          ++++ (* VR_vals *)
            right.
            invert_Forall2_app_r2 HForall2 vals' val1 val2 Hvals' Hval1 Hval2.
            rewrite upup_app; rewrite <- app_assoc; simpl.
            decompose_vals_as_E_seq_E vals'.
            exists S F. 
            destruct (eval_relop op val1 val2) as [ bval | ] eqn:Heval.
            +++++ (* Ok *)
              eexists;
                eapply SC_E;
                eapply SC_simple;
                eapply SS_relop...
            +++++ (* Err *)
              inverts Hval1 as Heqtype_of1.
              inverts Hval2 as Heqtype_of2.
              destruct (eval_relop_no_runtime_err op val1 val2 Heqtype_of1 Heqtype_of2 Heval).
          ++++ (* VR_trap *)
            step_VR_trap S F [Trap; Plain (Relop op)] [Plain (Relop op)].
        +++ (* ↪ *)
          step_snoc_app_cdr S' F' HSC [Plain (Relop op)].


      ++ (* VI_drop *)
        edestruct IHHVAIS as [HRT | HSC]; try solve [subst; eauto].
        +++ (* ⊢R *) 
          inverts HRT as HVR.
          inverts HVR as HForall2; simpl.
          ++++ (* VR_vals *)
            right.
            invert_Forall2_app_r1 HForall2 vals' val0 Hvals' Hval0.
            rewrite upup_app; rewrite <- app_assoc; simpl.
            decompose_vals_as_E_seq_E vals'.
            exists S F. eexists;
                eapply SC_E;
                eapply SC_simple;
                eapply SS_drop...
          ++++ (* VR_trap *)
            step_VR_trap S F [Trap; Plain Drop] [Plain Drop].
        +++ (* ↪ *)
          step_snoc_app_cdr S' F' HSC [Plain Drop].


      ++ (* VI_select *)
        edestruct IHHVAIS as [HRT | HSC]; try solve [subst; eauto].
        +++ (* ⊢R *) 
          inverts HRT as HVR.
          inverts HVR as HForall2; simpl.
          ++++ (* VR_vals *)
            right.
            invert_Forall2_app_r3 HForall2 vals' val1 val2 valc Hvals' Hval1 Hval2 Hvalc.
            rewrite upup_app; rewrite <- app_assoc; simpl.
            inverts Hvalc as Htypeof. 
            destruct valc as [c | | | ] ; inverts Htypeof. (* inverts our the underlying [I32.t] *)
            decompose_vals_as_E_seq_E vals'.
            exists S F.  
            destruct (I32.eqz c) eqn:Heqz;
              eexists;
              eapply SC_E;
              eapply SC_simple.
            +++++ eapply SS_select2...
            +++++ eapply SS_select1...
          ++++ (* VR_trap *)
            step_VR_trap S F [Trap; Plain Select] [Plain Select].
        +++ (* ↪ *)
          step_snoc_app_cdr S' F' HSC [Plain Select].


      ++ (* VI_nop *)
        edestruct IHHVAIS as [HRT | HSC]; try solve [subst; eauto].
        +++ (* ⊢R *) 
          inverts HRT as HVR.
          inverts HVR as HForall2; simpl.
          ++++ (* VR_vals *)
            right.
            decompose_vals_as_E_seq_E vals0.
            exists S F. eexists;
              eapply SC_E;
              eapply SC_simple;
              eapply SS_nop.
          ++++ (* VR_trap *)
            step_VR_trap S F [Trap; Plain Nop] [Plain Nop].
        +++ (* ↪ *)
          step_snoc_app_cdr S' F' HSC [Plain Nop].


      ++ (* VI_unreachable *)
        edestruct IHHVAIS as [HRT | HSC]; try solve [subst; eauto].
        +++ (* ⊢R *) 
          inverts HRT as HVR.
          inverts HVR as HForall2; simpl.
          ++++ (* VR_vals *)
            right.
            decompose_vals_as_E_seq_E vals0.
            exists S F. eexists;
              eapply SC_E;
              eapply SC_simple;
              eapply SS_unreachable.
          ++++ (* VR_trap *)
            step_VR_trap S F [Trap; Plain Unreachable] [Plain Unreachable].
        +++ (* ↪ *)
          step_snoc_app_cdr S' F' HSC [Plain Unreachable].


      ++ (* VI_block *)
        edestruct IHHVAIS as [HRT | HSC]; try solve [subst; eauto].
        +++ (* ⊢R *) 
          inverts HRT as HVR.
          inverts HVR as HForall2; simpl.
          ++++ (* VR_vals *)
            right.
            decompose_vals_as_E_seq_E vals0.
            exists S F. eexists;
              eapply SC_E;
              (* eapply SC_block *)
              admit.
          ++++ (* VR_trap *)
            step_VR_trap S F [Trap; Plain (Block bt instrs)] [Plain (Block bt instrs)].
        +++ (* ↪ *)
          step_snoc_app_cdr S' F' HSC [Plain (Block bt instrs)].


      ++ (* VI_loop *)
        edestruct IHHVAIS as [HRT | HSC]; try solve [subst; eauto].
        +++ (* ⊢R *) 
          inverts HRT as HVR.
          inverts HVR as HForall2; simpl.
          ++++ (* VR_vals *)
            right.
            decompose_vals_as_E_seq_E vals0.
            exists S F. eexists;
              eapply SC_E;
              (* eapply SC_loop *)
              admit.
          ++++ (* VR_trap *)
            step_VR_trap S F [Trap; Plain (Loop bt instrs)] [Plain (Loop bt instrs)].
        +++ (* ↪ *)
          step_snoc_app_cdr S' F' HSC [Plain (Loop bt instrs)].


      ++ (* VI_if *)
        edestruct IHHVAIS as [HRT | HSC]; try solve [subst; eauto].
        +++ (* ⊢R *) 
          inverts HRT as HVR.
          inverts HVR as HForall2; simpl.
          ++++ (* VR_vals *)
            right.
            decompose_vals_as_E_seq_E vals0.
            exists S F. eexists;
              eapply SC_E;
              (* eapply SC_if two cases *)
              admit.
          ++++ (* VR_trap *)
            step_VR_trap S F [Trap; Plain (If bt instrs1 instrs2)] [Plain (If bt instrs1 instrs2)].
        +++ (* ↪ *)
          step_snoc_app_cdr S' F' HSC [Plain (If bt instrs1 instrs2)].


      ++ (* VI_br *)
        edestruct IHHVAIS as [HRT | HSC]; try solve [subst; eauto].
        +++ (* ⊢R *) 
          inverts HRT as HVR.
          inverts HVR as HForall2; simpl.
          ++++ (* VR_vals *)
            (* We are not inside a label...how to step?
               SS_br require a label to br.
               This would be vacuously true. 
             *)
            admit.
          ++++ (* VR_trap *)
            step_VR_trap S F [Trap; Plain (Br l0)] [Plain (Br l0)].
        +++ (* ↪ *)
          step_snoc_app_cdr S' F' HSC [Plain (Br l0)].


      ++ (* VI_br_if *)
        edestruct IHHVAIS as [HRT | HSC]; try solve [subst; eauto].
        +++ (* ⊢R *) 
          inverts HRT as HVR.
          inverts HVR as HForall2; simpl.
          ++++ (* VR_vals *)
            right.
            rewrite app_assoc in HForall2.
            invert_Forall2_app_r1 HForall2 vals' val0 Hvals' Hval0.
            rewrite upup_app; rewrite <- app_assoc; simpl.
            decompose_vals_as_E_seq_E vals'.
            exists S F. 
            inverts Hval0 as Htypeof.
            destruct val0 as [ c | | | ]; inverts Htypeof.
            destruct (I32.eqz c) eqn:Heqz;
              eexists;
              eapply SC_E;
              eapply SC_simple.
            +++++ (* I32.eqz c = true  *) eapply SS_br_if2...
            +++++ (* I32.eqz c = false *) eapply SS_br_if1...
          ++++ (* VR_trap *)
            step_VR_trap S F [Trap; Plain (Br_if l0)] [Plain (Br_if l0)].
        +++ (* ↪ *)
          step_snoc_app_cdr S' F' HSC [Plain (Br_if l0)].

      ++ (* VI_br_table *)
        edestruct IHHVAIS as [HRT | HSC]; try solve [subst; eauto].
        +++ (* ⊢R *) 
          inverts HRT as HVR.
          inverts HVR as HForall2; simpl.
          ++++ (* VR_vals *)
            right.
            rewrite app_assoc in HForall2. rewrite app_assoc in HForall2.
            invert_Forall2_app_r1 HForall2 vals' val0 Hvals' Hval0.
            rewrite upup_app; rewrite <- app_assoc; simpl.
            decompose_vals_as_E_seq_E vals'.
            exists S F. 
            inverts Hval0 as Htypeof.
            destruct val0 as [ i | | | ]; inverts Htypeof.
            destruct (leb (length ls) (I32.to_nat i)) eqn:Hleb;
              eexists;
              eapply SC_E;
              eapply SC_simple.
            +++++ (* out of bound [SS_br_table__N] *)
              (* Need to make two numbers consistent *)
              admit.
            +++++ (* in bound [SS_br_table__i] *) 
              admit.
          ++++ (* VR_trap *)
            step_VR_trap S F [Trap; Plain (Br_table ls l__N)] [Plain (Br_table ls l__N)].
        +++ (* ↪ *)
          step_snoc_app_cdr S' F' HSC [Plain (Br_table ls l__N)].

    + (* VAI_trap *)
      edestruct IHHVAIS as [HRT | HSC]; try solve [subst; eauto].
      ++ (* ⊢R *) 
        inverts HRT as HVR.
        inverts HVR as HForall2; simpl. 
        +++ (* VR_vals *)
          right.
          decompose_vals_as_E_seq_E vals0.
          exists S F [Trap]. apply SC_trap__E.
        +++ (* VR_trap *)
            (* need to execute the first trap... though I doubt this case could happen? *)
          step_VR_trap S F [Trap; Trap] [Trap].
      ++ (* ↪ *)
        step_snoc_app_cdr S' F' HSC [Trap].

    + (* VAIS_label *)
      introv HVAIS__cont HVAIS__rest.
      inverts HVAIS__rest.
      ++ (* [] *) skip.
         (* TODO: need to generailize the context, i.e., the entire theorem *)

Admitted.

(** Archive - How I found it need to be a induction. *)

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



  
