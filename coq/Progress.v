(* ***************************************************************** *)
(* Progress.v                                                        *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)

(* ################################################################# *)
(** * Progress *)

From Wasm Require Export Validation.
From Wasm Require Export Execution.
From Wasm Require Export ExtendedTyping.
From Wasm Require Export ProofAux.
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
Qed.

Lemma F_ϵ_R: forall F,
    ⊢R (F, []) ∈ [].
Proof with eauto.
  intros.
  rewrite <- R_vals_ϵ...
Qed.

Lemma F_Trap_R: forall F rt,
    ⊢R (F, [Trap]) ∈ rt.
Proof with eauto.
  intros.
  asserts_rewrite ([Trap] = !R_trap)... 
Qed.


(* ================================================================= *)
(** ** Block Contexts *)

(* Push values onto the outermost level of a block context. *)
Definition B_prepend {k} (vals: list val) (B: block_context k) : block_context k :=
  match B with
  | B_nil vals' ainstrs => B_nil (vals ++ vals') ainstrs
  | B_cons vals' n cont B' ainstrs => B_cons (vals ++ vals') n cont B' ainstrs
  end.

(* Append instructions to the outermost level of a block context. *)
Definition B_append {k} (B: block_context k) (rest: list admin_instr) : block_context k :=
  match B with
  | B_nil vals ainstrs => B_nil vals (ainstrs ++ rest)
  | B_cons vals n cont B' ainstrs => B_cons vals n cont B' (ainstrs ++ rest)
  end.

Lemma plug_B_prepend : forall k (B: block_context k) vals hole,
    ⇈vals ++ plug__B B hole = plug__B (B_prepend vals B) hole.
Proof.
  intros. destruct B; simpl; rewrite upup_app, app_assoc; reflexivity.
Qed.

Lemma plug_B_append : forall k (B: block_context k) hole rest,
    plug__B B hole ++ rest = plug__B (B_append B rest) hole.
Proof.
  intros. destruct B; simpl; rewrite <- !app_assoc; reflexivity.
Qed.


(* ================================================================= *)
(** ** Stepping in Sequences *)

Lemma step_seq : forall S F vals ainstrs ainstrs' rest,
    (S, F, ainstrs) ↪ (S, F, ainstrs') ->
    (S, F, ⇈vals ++ ainstrs ++ rest) ↪ (S, F, ⇈vals ++ ainstrs' ++ rest).
Proof.
  introv HSC.
  apply (SC_E (E_seq vals E_hole rest)). assumption.
Qed.

Lemma step_simple_vals : forall S F vals ainstrs ainstrs',
    ainstrs ↪s ainstrs' ->
    (S, F, ⇈vals ++ ainstrs) ↪ (S, F, ⇈vals ++ ainstrs').
Proof.
  introv HSS.
  rewrite <- (app_nil_r ainstrs), <- (app_nil_r ainstrs').
  apply step_seq. constructor. assumption.
Qed.

Lemma step_trap_seq : forall S F vals rest,
    ⇈vals ++ [Trap] ++ rest <> [Trap] ->
    (S, F, ⇈vals ++ [Trap] ++ rest) ↪ (S, F, [Trap]).
Proof.
  introv Hneq.
  apply (SC_trap__E (E_seq vals E_hole rest)). assumption.
Qed.


(* ================================================================= *)
(** ** Values *)

Lemma type_of_i32 : forall (val: val),
    type_of val = T_i32 ->
    exists c, val = i32 c.
Proof.
  introv Heq. destruct val; inverts Heq. eauto.
Qed.

Lemma vbt_expand_some : forall C F bt ft,
    C.(C_types) = F.(A_module).(MI_types) ->
    C ⊢bt bt ∈ ft ->
    expand F bt = Some ft.
Proof.
  introv Htypes HVBT.
  inverts HVBT as; simpl; auto.
  introv Hi. rewrite <- Htypes. assumption.
Qed.


(* ================================================================= *)
(** ** Generalized Progress *)

(** A well-typed instruction sequence is either
    - a sequence of values,
    - a [Trap],
    - able to take a step, or
    - breaking out of the [k] labels of a block context [B] to the
      [j]-th label of the typing context, with as many values as that
      label expects. *)
Definition progress_result S F C ainstrs : Prop :=
  (exists vals, ainstrs = ⇈vals) \/
  ainstrs = [Trap] \/
  (exists ainstrs', (S, F, ainstrs) ↪ (S, F, ainstrs')) \/
  (exists k (B: block_context k) j vals ts,
      ainstrs = plug__B B (⇈vals ++ ↑[Br (k + j)]) /\
      C.(C_labels).[j] = Some ts /\
      length vals = length ts).

Scheme vai_mut_ind := Induction for valid_admin_instr Sort Prop
  with vais_mut_ind := Induction for valid_admin_instrs Sort Prop.

Lemma progress_ainstrs : forall S C ainstrs ts1 ts2,
    (S, C) ⊢a* ainstrs ∈ ts1 --> ts2 ->
    forall F vals,
      C.(C_types) = F.(A_module).(MI_types) ->
      map type_of vals = ts1 ->
      progress_result S F C (⇈vals ++ ainstrs).
Proof.
  introv HVAIS.
  apply (vais_mut_ind
    (fun SC ainstr ft _ =>
       let (S, C) := SC in let 'FT ts1 _ := ft in
       forall F vals,
         C.(C_types) = F.(A_module).(MI_types) ->
         map type_of vals = ts1 ->
         progress_result S F C (⇈vals ++ [ainstr]))
    (fun SC ainstrs ft _ =>
       let (S, C) := SC in let 'FT ts1 _ := ft in
       forall F vals,
         C.(C_types) = F.(A_module).(MI_types) ->
         map type_of vals = ts1 ->
         progress_result S F C (⇈vals ++ ainstrs)))
    with (p := (S, C)) (f := ts1 --> ts2) in HVAIS; [exact HVAIS | ..];
    clear S C ainstrs ts1 ts2 HVAIS.
  all: simpl.

  - (* VAI_instr *)
    introv HVI. destruct ft as [ts1 ts2]. simpl.
    introv Htypes Hvals.
    revert Hvals. inversion HVI; subst; clear HVI; intros Hvals.

    + (* VI_const *)
      left. exists (vals ++ [val]). rewrite upup_app. reflexivity.

    + (* VI_unop *)
      destruct vals as [ | val [ | ]]; inverts Hvals as Hval.
      right; right; left.
      destruct (eval_unop op val) as [[val' | ] | ] eqn:Heval.
      * eexists. apply SC_simple. apply SS_unop__some. eassumption.
      * eexists. apply SC_simple. apply SS_unop__none. eassumption.
      * exfalso. eapply eval_unop_no_runtime_err; [ | eassumption]; congruence.

    + (* VI_binop *)
      destruct vals as [ | val1 [ | val2 [ | ]]]; inverts Hvals as Hval1 Hval2.
      right; right; left.
      destruct (eval_binop op val1 val2) as [[val' | ] | ] eqn:Heval.
      * eexists. apply SC_simple. apply SS_binop__some. eassumption.
      * eexists. apply SC_simple. apply SS_binop__none. eassumption.
      * exfalso. eapply eval_binop_no_runtime_err; [ | | eassumption]; congruence.

    + (* VI_testop *)
      destruct vals as [ | val [ | ]]; inverts Hvals as Hval.
      right; right; left.
      destruct (eval_testop op val) as [b | ] eqn:Heval.
      * eexists. apply SC_simple. apply SS_testop. eassumption.
      * exfalso. eapply eval_testop_no_runtime_err; [ | eassumption]; congruence.

    + (* VI_relop *)
      destruct vals as [ | val1 [ | val2 [ | ]]]; inverts Hvals as Hval1 Hval2.
      right; right; left.
      destruct (eval_relop op val1 val2) as [b | ] eqn:Heval.
      * eexists. apply SC_simple. apply SS_relop. eassumption.
      * exfalso. eapply eval_relop_no_runtime_err; [ | | eassumption]; congruence.

    + (* VI_drop *)
      destruct vals as [ | val [ | ]]; inverts Hvals.
      right; right; left.
      eexists. apply SC_simple. apply SS_drop.

    + (* VI_select *)
      destruct vals as [ | val1 [ | val2 [ | val3 [ | ]]]]; inverts Hvals.
      match goal with Hval3 : type_of val3 = T_i32 |- _ =>
        apply type_of_i32 in Hval3 as [c ->] end.
      right; right; left.
      destruct (I32.eqz c) eqn:Heqz.
      * eexists. apply SC_simple. apply SS_select2. assumption.
      * eexists. apply SC_simple. apply SS_select1. assumption.

    + (* VI_nop *)
      destruct vals; inverts Hvals.
      right; right; left.
      eexists. apply SC_simple. apply SS_nop.

    + (* VI_unreachable *)
      right; right; left.
      eexists. apply step_simple_vals. apply SS_unreachable.

    + (* VI_block *)
      right; right; left.
      match goal with HVBT : _ ⊢bt _ ∈ ?ts1 --> ?ts2 |- _ =>
        eexists; eapply SC_block with (ts1 := ts1) (ts2 := ts2);
          [ reflexivity | reflexivity
          | rewrite <- Hvals, map_length; reflexivity
          | eapply vbt_expand_some; eassumption ] end.

    + (* VI_loop *)
      right; right; left.
      match goal with HVBT : _ ⊢bt _ ∈ ?ts1 --> ?ts2 |- _ =>
        eexists; eapply SC_loop with (ts1 := ts1) (ts2 := ts2);
          [ reflexivity | reflexivity
          | rewrite <- Hvals, map_length; reflexivity
          | eapply vbt_expand_some; eassumption ] end.

    + (* VI_if *)
      apply map_eq_app in Hvals as (vals1 & vals2 & -> & Hvals1 & Hvals2).
      destruct vals2 as [ | val [ | ]]; inverts Hvals2 as Hval.
      apply type_of_i32 in Hval as [c ->].
      rewrite upup_app, <- app_assoc.
      right; right; left.
      match goal with HVBT : _ ⊢bt bt ∈ _ --> _ |- _ =>
        pose proof (vbt_expand_some _ _ _ _ Htypes HVBT) as Hexpand end.
      destruct (I32.eqz c) eqn:Heqz;
        [ eexists; eapply SC_if__eqz with (vals := vals1)
        | eexists; eapply SC_if__nez with (vals := vals1) ];
        try eassumption; try reflexivity;
        rewrite <- Hvals1, map_length; reflexivity.

    + (* VI_br *)
      apply map_eq_app in Hvals as (vals1 & vals2 & -> & Hvals1 & Hvals2).
      right; right; right.
      exists 0 (B_nil vals1 []) l vals2 ts.
      splits; auto.
      * simpl. rewrite upup_app, <- app_assoc, app_nil_r. reflexivity.
      * rewrite <- Hvals2, map_length. reflexivity.

    + (* VI_br_if *)
      apply map_eq_app in Hvals as (vals1 & vals2 & -> & Hvals1 & Hvals2).
      destruct vals2 as [ | val [ | ]]; inverts Hvals2 as Hval.
      apply type_of_i32 in Hval as [c ->].
      rewrite upup_app, <- app_assoc.
      right; right; left.
      destruct (I32.eqz c) eqn:Heqz.
      * eexists. apply step_simple_vals. apply SS_br_if2. assumption.
      * eexists. apply step_simple_vals. apply SS_br_if1. assumption.

    + (* VI_br_table *)
      apply map_eq_app in Hvals as (vals1 & vals2 & -> & Hvals1 & Hvals2).
      apply map_eq_app in Hvals2 as (vals2' & vals3 & -> & Hvals2 & Hvals3).
      destruct vals3 as [ | val [ | ]]; inverts Hvals3 as Hval.
      apply type_of_i32 in Hval as [c ->].
      rewrite !upup_app, <- !app_assoc, app_assoc, <- upup_app.
      right; right; left.
      destruct (nth_error ls (I32.to_nat c)) as [l__i | ] eqn:Hnth.
      * eexists. apply step_simple_vals. apply SS_br_table__i. eassumption.
      * eexists. apply step_simple_vals. apply SS_br_table__N.
        apply nth_error_None. assumption.

  - (* VAI_trap *)
    introv _ Htypes Hvals.
    destruct vals as [ | val vals].
    + right; left. reflexivity.
    + right; right; left.
      eexists. rewrite <- (app_nil_r [Trap]).
      apply step_trap_seq. simpl. discriminate.

  - (* VAI_label *)
    introv Hn HVAIS__cont IH__cont HVAIS__body IH__body.
    introv Htypes Hvals.
    destruct vals; inverts Hvals. simpl.
    destruct (IH__body F [] Htypes eq_refl)
      as [(vals & Hbody) | [Hbody | [(body' & HSC) | (k & B & j & vals & ts & Hbody & Hj & Hlen)]]];
      simpl in *; subst.
    + (* body is values *)
      right; right; left.
      eexists. apply SC_simple. eapply SS_block__exit. reflexivity.
    + (* body is [Trap] *)
      right; right; left.
      eexists. apply (SC_trap__E (E_label (length ts1) ainstrs0 E_hole)).
      simpl. discriminate.
    + (* body steps *)
      right; right; left.
      eexists. apply (SC_E (E_label (length ts1) ainstrs0 E_hole)). eassumption.
    + (* body breaks *)
      destruct j as [ | j]; simpl in Hj.
      * (* to this label *)
        inverts Hj.
        right; right; left.
        rewrite Nat.add_0_r in *.
        eexists. apply SC_simple. apply SS_br. assumption.
      * (* to an outer label *)
        right; right; right.
        exists (k + 1) (B_cons [] (length ts1) ainstrs0 B []) j vals ts.
        splits; auto.
        simpl. replace (k + 1 + j) with (k + Datatypes.S j) by lia.
        reflexivity.

  - (* VAIS_empty *)
    introv Htypes Hvals.
    left. exists vals. rewrite app_nil_r. reflexivity.

  - (* VAIS_snoc *)
    introv HVAIS IH HVAI IH__N Htypes Hvals.
    destruct (IH F vals Htypes Hvals)
      as [(vals' & Hvals') | [Htrap | [(ainstrs' & HSC) | (k & B & j & vals' & ts' & Hbreak & Hj & Hlen)]]].
    + (* values: look at the last instruction *)
      assert (Htypes' : map type_of vals' = ts0 ++ ts).
      { assert (HVAIS' : (S, C) ⊢a* ⇈vals ++ ainstrs ∈ [] --> (ts0 ++ ts)).
        { apply vais_app. exists ts1. split; auto.
          rewrite <- Hvals. apply vais_vals_intro. }
        rewrite Hvals' in HVAIS'.
        apply vais_vals in HVAIS'. auto. }
      apply map_eq_app in Htypes' as (vals0 & vals1 & -> & _ & Hvals1).
      rewrite app_assoc, Hvals', upup_app, <- app_assoc.
      destruct (IH__N F vals1 Htypes Hvals1)
        as [(vals2 & Hvals2) | [Htrap | [(ainstrs' & HSC) | (k & B & j & vals2 & ts' & Hbreak & Hj & Hlen)]]].
      * left. exists (vals0 ++ vals2). rewrite Hvals2, upup_app. reflexivity.
      * rewrite Htrap.
        destruct vals0 as [ | val vals0].
        -- right; left. reflexivity.
        -- right; right; left.
           eexists. rewrite <- (app_nil_r [Trap]).
           apply step_trap_seq. simpl. discriminate.
      * right; right; left.
        eexists. rewrite <- (app_nil_r (⇈vals1 ++ [ainstr__N])).
        apply step_seq. eassumption.
      * right; right; right.
        exists k (B_prepend vals0 B) j vals2 ts'.
        rewrite Hbreak, plug_B_prepend. auto.
    + (* trap *)
      rewrite app_assoc, Htrap.
      right; right; left.
      eexists. rewrite <- (app_nil_l ([Trap] ++ [ainstr__N])).
      apply (step_trap_seq _ _ []). simpl. discriminate.
    + (* step *)
      rewrite app_assoc.
      right; right; left.
      eexists. rewrite <- (app_nil_l ((⇈vals ++ ainstrs) ++ [ainstr__N])).
      apply (step_seq _ _ []). eassumption.
    + (* break *)
      rewrite app_assoc, Hbreak, plug_B_append.
      right; right; right.
      exists k (B_append B [ainstr__N]) j vals' ts'. auto.
Qed.


(* ================================================================= *)
(** ** Progress - Main Theorem *)

Lemma valid_frame_labels : forall S F C,
    S ⊢A F ∈ C ->
    C.(C_labels) = [].
Proof.
  introv HVA.
  inverts HVA as HVMI.
  inverts HVMI.
  reflexivity.
Qed.

Lemma Forall2_valid_values : forall vals,
    Forall2 (fun val t => ⊢v val ∈ t) vals (map type_of vals).
Proof.
  induction vals; simpl; auto.
Qed.

Theorem progress : forall S T rt,
    ⊢c (S, T) ∈ rt ->
    ⊢R T ∈ rt \/ exists S' F' ainstrs', $(S, T) ↪ (S', F', ainstrs').
Proof with eauto.
  introv HVC.
  inverts HVC as HVS HVT.
  inverts HVT as HVA HVAIS.
  destruct (progress_ainstrs _ _ _ _ _ HVAIS F [] (valid_frame_types _ _ _ HVA) eq_refl)
    as [(vals & Hvals) | [Htrap | [(ainstrs' & HSC) | (k & B & j & vals & ts & _ & Hj & _)]]];
    simpl in *; auto.

  - (* values *)
    left. subst.
    apply vais_vals in HVAIS. simpl in HVAIS. subst.
    apply F_vals_R. apply Forall2_valid_values.

  - (* [Trap] *)
    left. subst. apply F_Trap_R.

  - (* step *)
    right...

  - (* a break cannot escape the top level *)
    erewrite valid_frame_labels in Hj; eauto.
    destruct j; inverts Hj.
Qed.
