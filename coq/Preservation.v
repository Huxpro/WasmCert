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

(* ----------------------------------------------------------------- *)
(** *** VAIS lemma *)

(* As all VAIS rule, this lemma merge the weakening rules *)
Lemma vals_vais: forall S C vals ts1 ts2, 
    (S,C) ⊢a* ⇈vals ∈ ts1 --> ts2 ->
    ts2 = ts1 ++ map type_of vals.
Proof with auto.
  introv HVAIS.
  dependent induction HVAIS;
    rename x into Heq;
    symmetry in Heq.

  - (* VAIS_empty *)
    apply map_eq_nil in Heq;
      apply map_eq_nil in Heq;
      subst;
      simpl.
    rewrite app_nil_r...
  - (* VAIS_snoc *)
    rename H into HVAI__N.
    apply map_eq_snoc_app_split in Heq.
    destruct Heq as (instrs & instr__N & Heq & Hinstrs & Hinstr__N).
    apply map_eq_snoc_app_split in Heq.
    destruct Heq as (vals' & val__N & Heq & Hvals' & Hval__N).

    rewrite <- Hinstrs in *.
    rewrite <- Hinstr__N in *.
    rewrite <- Hvals' in *.
    rewrite <- Hval__N in *.

    inverts HVAI__N as HVI__N.
    inverts HVI__N.

    asserts_rewrite (map type_of vals = map type_of vals' ++ [type_of val__N]).
    + rewrite -> Heq. apply map_app.
    + rewrite app_assoc.
      apply snoc_app_inj.
      split...
      ++ eapply (IHHVAIS S C vals' ts1 ts0)...
         rewrite app_nil_r...
Qed.

Lemma vals_typing_eq: forall S C vals rt, 
    (S,C) ⊢a* ⇈vals ∈ [] --> rt ->
    rt = map type_of vals.
Proof with auto.
  introv HVAIS.
  dependent induction HVAIS;
    rename x into Heq;
    symmetry in Heq.
  - (* VAIS_nil *)
    apply map_eq_nil in Heq.
    apply map_eq_nil in Heq.
    subst...
  - (* VAIS_snoc *)
    rename H into HVAI__N.
    apply map_eq_snoc_app_split in Heq.
    destruct Heq as (instrs & instr__N & Heq & Hinstrs & Hinstr__N).
    apply map_eq_snoc_app_split in Heq.
    destruct Heq as (vals' & val__N & Heq & Hvals' & Hval__N).

    rewrite <- Hinstrs in *.
    rewrite <- Hinstr__N in *.
    rewrite <- Hvals' in *.
    rewrite <- Hval__N in *.

    inverts HVAI__N as HVI__N.
    inverts HVI__N.

    asserts_rewrite (map type_of vals = map type_of vals' ++ [type_of val__N]).
    + rewrite -> Heq. apply map_app.
    + apply snoc_app_inj.
      split...
      ++ rewrite <- (app_nil_r ts0). 
         eapply (IHHVAIS S C vals' (ts0 ++ []))...
Qed.



(* ================================================================= *)
(** ** Lemma - Normal Form *)

Definition normal_form {X : Type} (R : relation X) (x : X) : Prop :=
  ~ exists x', R x x'.

Lemma vals_normal_form_step_simple : forall vals,
    normal_form step_simple (⇈vals).
Proof.
  unfold normal_form. introv. intros H.
  inverts H as. intros ainstrs' HSC.
  inverts HSC; (* will name evidence as H0, H... *)
  (* TODO : extract Ltac similar to [invert_eq_snoc_app] for vals *)
  (* Drop - no condition, H0 is the Heq *)
  try (rename H0 into H);  
  (* Numerics & Select, H0 for some condition, H for the Heq *)
  try (apply eq_unsnoc_car_eq in H; simpl in *;
       specialize (unsnoc_car_vals vals) as [Hnone | Hsome];
       try (rewrite -> Hnone in H; inverts H);
       try (destruct Hsome as [x Hx]; rewrite -> Hx in H; inverts H)).
Qed.

(* 

Not True

Lemma vals_is_normal_form_step : forall S F vals,
    normal_form step (S, F, ⇈vals).
Proof with auto.
  unfold normal_form. introv. intros H.
  inverts H as. intros ainstrs' HSS.
  inverts HSS.
  - (* SS_simple *)
    apply (vals_is_normal_form_step_simple vals).
    exists ainstrs'0...
  - (* SS_E *)
*)

Lemma plug_E_ϵ : forall E ainstrs, 
    plug__E E ainstrs = [] ->     (* N.B. not vice versa *)
    ainstrs = [].
Proof.
  introv H.
  induction E.
  - (* E_hole *)
    simpl in *. assumption.
  - (* E_seq *)
    simpl in *. 
    apply app_eq_nil in H. destruct H.
    apply app_eq_nil in H0. destruct H0.
    apply IHE. assumption.
  - (* E_label *)
    simpl in *. 
    inverts H.
Qed.

Lemma plug_B_ϵ : forall k (B : block_context k) ainstrs, 
    plug__B B ainstrs = [] ->     (* N.B. not vice versa *)
    ainstrs = [].
Proof.
  introv H.
  induction B.
  - (* B_nil *)
    simpl in *.
    apply app_eq_nil in H. destruct H.
    apply app_eq_nil in H0. destruct H0.
    assumption.
  - (* B_cons *)
    simpl in *. 
    apply app_eq_nil in H. destruct H.
    inverts H0.
Qed.

(* snoc a [val] should be either ill-formed or, normally, all [val] *)
Lemma ainstrs_snoc_app_val_normal_form_step_simple: forall ainstrs val, 
    normal_form step_simple (ainstrs ++ ⇈[val]).
Proof.
  unfold normal_form. introv. intros H.
  inverts H as. intros ainstrs' HSC.
  inverts HSC;
  try invert_eq_snoc_app H;
  try invert_eq_snoc_app H0.
Qed.
      
Lemma instrs_snoc_app_val_normal_form_step_simple: forall instrs val, 
    normal_form step_simple (↑(instrs ++ [Const val])).
Proof.
  intros.
  specialize (map_app Plain instrs [Const val]). intros.
  rewrite H.
  apply ainstrs_snoc_app_val_normal_form_step_simple.
Qed.

Lemma S_F_ϵ_is_normal_form : forall S F S' F',
  ~ exists ainstrs', (S, F, []) ↪ (S', F', ainstrs').
Proof with auto.
  introv. intros HS.
  inverts HS as. intros ainstrs' HSC.

  (* want both inversion and induction? [remember] *)
  remember (S, F, []) as S_F_ϵ.     

  induction HSC;
    inverts HeqS_F_ϵ as;

  (* SC_simple *)
  try (inversion H);

  (* SC_block *) (* SC_loop *)
  try (intros Heq; symmetry in Heq; invert_eq_snoc_app Heq);

  (* SC_if1 *) (* SC_if2 *)
  try (intros Heq; symmetry in Heq;
       rewrite snoc_app2_as_snoc_app in Heq;
       invert_eq_snoc_app Heq).

  - (* SC_E *)
    intros HE.
    apply plug_E_ϵ in HE; subst.
    apply IHHSC...

  - (* [SC_trap__E] *)
    intros HE.
    apply plug_E_ϵ in HE; subst.
    inverts HE.
Qed.


(* ================================================================= *)
(** ** Lemma - VAIS append  *)

(*
   ts1 --> [  ainstrs0  |  ainstrs1 ] --> ts3
   ts1 --> [  ainstrs0  ] --> ts2
                ts2 --> [  ainstrs1 ] --> ts3
 *)
Lemma vais_app : forall S C ainstrs0 ainstrs1 ts1 ts3,
  (S, C) ⊢a* ainstrs0 ++ ainstrs1 ∈ ts1 --> ts3 <->
  exists ts2,
    (S, C) ⊢a* ainstrs0 ∈ ts1 --> ts2
  /\ (S, C) ⊢a* ainstrs1 ∈ ts2 --> ts3.
Proof with eauto.
  split.
  --- (* -> *)
  introv HVAISapp.
  dependent induction HVAISapp;
    rename x into Heqapp.
  - symmetry in Heqapp. apply app_eq_nil in Heqapp.
    inverts Heqapp. eexists. split...
  - destruct ainstrs1 as [ | ai ais].
    + destruct ainstrs0 as [ | ai ais ].
      ++ simpl in Heqapp. symmetry in Heqapp.
         invert_eq_snoc_app_compute Heqapp.
      ++ (*
           [ ainstrs ] ++ [ainstr__N]
           [ ainstrs0             ] 
       *)
        destruct (cons_to_snoc_app ai ais) as (ainstrs1' & ainstr1__N & Heq).
        rewrite Heq in *.
        rewrite app_nil_r in Heqapp.
        eapply snoc_app_inj in Heqapp.
        inverts Heqapp. 
        eexists.
        split...
    + (*
           [ ainstrs0 | ainstrs1'] ++ [ainstr__N]
           [ ainstrs0 | ainstrs1              ] 
       *)
      destruct (cons_to_snoc_app ai ais) as (ainstrs1' & ainstr1__N & Heq).
      rewrite Heq in *.
      rewrite app_assoc in Heqapp.
      eapply snoc_app_inj in Heqapp.
      inverts Heqapp. 
      edestruct IHHVAISapp as (ts4' & HV1 & HV2)...
  --- (* <- *)
Admitted.    


(*
   ts1 --> [  ainstrs0  |  ainstrs1  |  ainstrs2  ] --> ts4
   ts1 --> [  ainstrs0  ] --> ts2
                ts2 --> [  ainstrs1 ] --> ts3
                             ts3 --> [  ainstrs1  ] --> ts4
 *)
Lemma vais_app3 : forall S C ainstrs0 ainstrs1 ainstrs2 ts1 ts4,
  (S, C) ⊢a* ainstrs0 ++ ainstrs1 ++ ainstrs2 ∈ ts1 --> ts4 <->
  exists ts2 ts3,
    (S, C) ⊢a* ainstrs0 ∈ ts1 --> ts2
  /\ (S, C) ⊢a* ainstrs1 ∈ ts2 --> ts3
  /\ (S, C) ⊢a* ainstrs2 ∈ ts3 --> ts4.
Proof with eauto.
  split.
  - (* -> *)
    introv Happ3.
    apply vais_app in Happ3.
    destruct Happ3 as (ts2 & Hainstrs0 & Happ2).
    apply vais_app in Happ2.
    destruct Happ2 as (ts3 & Hainstrs1 & Hainstrs2).
    exists ts2 ts3...
  - (* <- *)
    intros (ts2 & ts3 & H0 & H1 & H2).
    apply vais_app. exists ts2. split...
    apply vais_app. exists ts3. split...
Qed.

Lemma vais_ts0_ϵ: forall S C ts0,
        (S, C) ⊢a* [] ∈ [] --> (ts0 ++ []) ->
        ts0 = [].
Proof with eauto.
  introv HVAIS.
  inverts HVAIS.
  ++ symmetry in H3. apply app_eq_nil in H3. destruct H3...
  ++ symmetry in H1. invert_eq_snoc_app H1.
Qed.
      

(* ================================================================= *)
(** ** Lemma - Unproved/Unused *)

            
Lemma vais_singleton: forall S C ainstr ts1 ts2,
        (S, C) ⊢a* [ainstr] ∈ ts1 --> ts2 <->
        (S, C) ⊢a ainstr ∈ ts1 --> ts2.
Proof with eauto.
  split. 
  (* -> *)
  - introv HVAIS.
    inverts HVAIS as HVAIS' HVAI__N Heq.
    rewrite <- app_nil_l in Heq.
    apply snoc_app_inj in Heq.
    destruct Heq; subst.
    inverts HVAIS'.
    + skip.
Admitted.



(* ================================================================= *)
(** ** Preservation - VAIS_snoc -> SC_simple*)


Lemma preservation_SC_simple_gen : forall S C ainstrs ainstr__N ainstrs' ts0 ts1 ts2 ts3,
      (S,C) ⊢a* ainstrs ∈ ts1 --> (ts0 ++ ts2)  -> (* [HVAIS] *)
      (S,C) ⊢a  ainstr__N ∈ ts2 --> ts3 ->          (* [HVAI__N] *)
      ainstrs ++ [ainstr__N] ↪s ainstrs' ->        (* [HSS] *)
(* -------------------------------------------------------------- *)
      (S,C) ⊢a* ainstrs' ∈ ts1 --> (ts0 ++ ts3).
Proof with eauto.
  introv HVAIS HVAI__N HSS.
  inverts HVAI__N as.

  - (* VAI_instr *)
    intros HVI__N.
    inverts HVI__N as;

    (* cases not could not take a simple step
       - VI_const
       - VI_block
       - VI_loop
       - VI_if
       - VI_br
     *)
    try solve [
          inverts keep HSS; 
          try invert_eq_snoc_app H0;
          try invert_eq_snoc_app H].

    + (* VI_unop *)
      inverts keep HSS as Heval Heq;
        try invert_eq_snoc_app Heval;
        try invert_eq_snoc_app Heq. 

      ++ (* [SS_unop__some] *)
        rewrite <- (app_nil_l (↑[Const val])).
        apply VAIS_snoc with (ts := []). 

        +++ (* [] *)



          apply vals_vais with (vals := [val1]) in HVAIS. simpl in HVAIS.
          apply snoc_app_inj in HVAIS. destruct HVAIS as (Heqts0 & Htypeof).
          subst. rewrite app_nil_r. constructor.

        +++ (* ↑[Const val] *)
          apply VAI_instr.
          apply VI_const.
          apply eval_unop_preserve_type in Heval...
Admitted. 


Lemma preservation_SC_simple : forall S C ainstrs ainstr__N ainstrs' ts0 ts2 ts3,
      (S,C) ⊢a* ainstrs ∈ [] --> (ts0 ++ ts2)  -> (* [HVAIS] *)
      (S,C) ⊢a  ainstr__N ∈ ts2 --> ts3 ->          (* [HVAI__N] *)
      ainstrs ++ [ainstr__N] ↪s ainstrs' ->        (* [HSS] *)
(* -------------------------------------------------------------- *)
      (S,C) ⊢a* ainstrs' ∈ [] --> (ts0 ++ ts3).
Proof with eauto.
  introv HVAIS HVAI__N HSS.
  inverts HVAI__N as.

  - (* VAI_instr *)
    intros HVI__N.
    inverts HVI__N as;

    (* cases not could not take a simple step
       - VI_const
       - VI_block
       - VI_loop
       - VI_if
       - VI_br
     *)
    try solve [
          inverts keep HSS; 
          try invert_eq_snoc_app H0;
          try invert_eq_snoc_app H].

    + (* VI_unop *)
      inverts keep HSS as Heval Heq;
        try invert_eq_snoc_app Heval;
        try invert_eq_snoc_app Heq. 

      ++ (* [SS_unop__some] *)
        rewrite <- (app_nil_l (↑[Const val])).
        apply VAIS_snoc with (ts := []). 

        +++ (* [] *)
          specialize (vals_typing_eq S C [val1] _ HVAIS) as Heq; simpl in Heq.
          destruct (snoc_app_eq_unit _ _ _ Heq) as (Htype_of & Heqts0).
          subst. constructor.

        +++ (* ↑[Const val] *)
          apply VAI_instr.
          apply VI_const.
          apply eval_unop_preserve_type in Heval...

      ++ (* [SS_unop__none] *)
        rewrite <- (app_nil_l ([Trap])).
        apply VAIS_snoc with (ts := []). 

        +++ (* [] *)
          specialize (vals_typing_eq S C [val1] _ HVAIS) as Heq; simpl in Heq.
          destruct (snoc_app_eq_unit _ _ _ Heq) as (Htype_of & Heqts0).
          subst. constructor.

        +++ (* [Trap] *)
          apply VAI_trap.


    + (* VI_binop *)
      inverts keep HSS as Heval Heq; 
        try invert_eq_snoc_app Heval;
        try invert_eq_snoc_app Heq. 

      ++ (* [SS_binop__some] *)
        rewrite <- (app_nil_l (↑[Const val])).
        apply VAIS_snoc with (ts := []).

        +++ (* [] *)
          specialize (vals_typing_eq S C [val1; val2] _ HVAIS) as Heq; simpl in Heq.
          destruct (snoc_app_eq_same_len ts0 [type_of op; type_of op] [type_of val1; type_of val2])... 
          subst. constructor.

        +++ (* ↑[Const val] *)
          apply VAI_instr.
          apply VI_const.
          apply eval_binop_preserve_type in Heval...

      ++ (* [SS_binop__none] *)
        rewrite <- (app_nil_l ([Trap])).
        apply VAIS_snoc with (ts := []). (* We know [ts] from [Const val]*)

        +++ (* [] *)
          specialize (vals_typing_eq S C [val1; val2] _ HVAIS) as Heq; simpl in Heq.
          destruct (snoc_app_eq_same_len ts0 [type_of op; type_of op] [type_of val1; type_of val2])... 
          subst. constructor.

        +++ (* [Trap] *)
          apply VAI_trap.


    + (* VI_testop *)
      inverts keep HSS as Heval Heq; 
        try invert_eq_snoc_app Heval;
        try invert_eq_snoc_app Heq. 

      ++ (* [SS_testop] *)
        rewrite <- (app_nil_l (↑[Const b])).
        apply VAIS_snoc with (ts := []).

        +++ (* [] *)
          specialize (vals_typing_eq S C [val1] _ HVAIS) as Heq; simpl in Heq.
          destruct (snoc_app_eq_unit _ _ _ Heq)... 
          subst. constructor.

        +++ (* ↑[Const b] *)
          apply VAI_instr.
          apply VI_const.
          simpl... 


    + (* VI_relop *)
      inverts keep HSS as Heval Heq; 
        try invert_eq_snoc_app Heval;
        try invert_eq_snoc_app Heq. 

      ++ (* [SS_testop] *)
        rewrite <- (app_nil_l (↑[Const b])).
        apply VAIS_snoc with (ts := []).

        +++ (* [] *)
          specialize (vals_typing_eq S C [val1; val2] _ HVAIS) as Heq; simpl in Heq.
          destruct (snoc_app_eq_same_len ts0 [type_of op; type_of op] [type_of val1; type_of val2])... 
          subst. constructor.

        +++ (* ↑[Const b] *)
          apply VAI_instr.
          apply VI_const.
          simpl... (* ??? *) (* apply eval_relop_preserve_type in Heval... *)


    + (* VI_drop *)
      inverts keep HSS; 
        try invert_eq_snoc_app H0;
        try invert_eq_snoc_app H.

      ++ (* [SS_drop] *)
        specialize (vals_typing_eq S C [val] _ HVAIS) as Heq; simpl in Heq.
        destruct (snoc_app_eq_unit _ _ _ Heq)... 
        subst. constructor.


    + (* VI_select *)
      inverts keep HSS; 
        try invert_eq_snoc_app H0;
        try invert_eq_snoc_app H.

      ++ (* [SS_select1] *)
        rewrite <- (app_nil_l (↑[Const val1])).
        apply VAIS_snoc with (ts := []);

          specialize (vals_typing_eq S C [val1; val2; (i32 c)] _ HVAIS) as Heq; simpl in Heq;
          destruct (snoc_app_eq_same_len ts0 [t; t; T_i32] [type_of val1; type_of val2; T_i32])... 

        +++ (* [] *)
          subst. constructor.

        +++ (* ↑[Const val1] *)
          inverts H1.
          apply VAI_instr.
          apply VI_const.
          simpl... 

      ++ (* [SS_select2] *)
        rewrite <- (app_nil_l (↑[Const val2])).
        apply VAIS_snoc with (ts := []);

          specialize (vals_typing_eq S C [val1; val2; (i32 c)] _ HVAIS) as Heq; simpl in Heq;
          destruct (snoc_app_eq_same_len ts0 [t; t; T_i32] [type_of val1; type_of val2; T_i32])... 

        +++ (* [] *)
          subst. constructor.

        +++ (* ↑[Const val2] *)
          inverts H1.
          apply VAI_instr.
          apply VI_const.
          simpl... 


    + (* VI_nop *)
      inverts keep HSS; 
        try invert_eq_snoc_app H0;
        try invert_eq_snoc_app H.
      apply HVAIS.


    + (* VI_unreachable *)
      inverts keep HSS; 
        try invert_eq_snoc_app H0;
        try invert_eq_snoc_app H.

      inverts HVAIS as Heq. 
      ++ (* VAIS_empty *)
        symmetry in Heq.
        apply app_eq_nil in Heq.
        destruct Heq; subst.
        rewrite <- (app_nil_l ([Trap])).
        apply VAIS_snoc with (ts := []); constructor.
      ++ (* VAIS_snoc *)
        symmetry in H1.
        invert_eq_snoc_app_compute H1.

    + (* VI_br_if *)
      intros Hl0.
      inverts keep HSS; 
        try invert_eq_snoc_app H0;
        try invert_eq_snoc_app H;

          specialize (vals_typing_eq S C [(i32 c)] _ HVAIS) as Heq; simpl in Heq;
          rewrite app_assoc in Heq;
          destruct (snoc_app_eq_same_len (ts0++ts3) [T_i32] [T_i32]); eauto;
          apply app_eq_nil in H; destruct H; subst.

      ++ (* [SS_br_if1 ↪ br] *)
        rewrite <- (app_nil_l (↑[Br l0])).
        eapply VAIS_snoc with (ts := []).
        +++ (* [] *) eauto.
        +++ (* [Br l0] *)
          eapply VAI_instr.
          eapply VI_br with (ts1 := [])...
        
      ++ (* [SS_br_if2 ↪ ϵ]  *)
        eauto.


    + (* VI_br_table *)
      intros Hls Hl__N.
      inverts keep HSS; 
        try invert_eq_snoc_app H0;
        try invert_eq_snoc_app H;

          remember (nat_to_i32 i) as c;
          specialize (vals_typing_eq S C [(i32 c)] _ HVAIS) as Heq; simpl in Heq;
          rewrite app_assoc in Heq; rewrite app_assoc in Heq;
          destruct (snoc_app_eq_same_len ((ts0 ++ ts1) ++ ts) [T_i32] [T_i32]); eauto;
          apply app_eq_nil in H; destruct H; 
            apply app_eq_nil in H; destruct H;
              subst.

      ++ (* [SS_br_table__i] *)
        rewrite <- (app_nil_l (↑[Br l__i])).
        eapply VAIS_snoc with (ts := []).
        +++ (* [] *) eauto.
        +++ (* [Br l__i] *)
          eapply VAI_instr.
          eapply VI_br with (ts1 := [])...
          eapply Forall_forall with (x := l__i) in Hls...
          eapply nth_error_In...

      ++ (* [SS_br_table__N] *)
        rewrite <- (app_nil_l (↑[Br l__N])).
        eapply VAIS_snoc with (ts := []).
        +++ (* [] *) eauto.
        +++ (* [Br l__N] *)
          eapply VAI_instr.
          eapply VI_br with (ts1 := [])...


  - (* VAI_label *)
    inverts keep HSS;
      try invert_eq_snoc_app H0; 
      try invert_eq_snoc_app H.


  - (* VAI_label *)
    introv HVAIS__cont HVAIS__rest.
    (*
       [HSS :       ainstrs ++ [Label (length ts1) instrs0 ainstrs0] ↪s ainstrs'
       [HVAIS__cont : (S, C) ⊢a* ↑ instrs0 ∈ ts1 --> ts3
       [HVAIS__rest : (S, C,labels ts1) ⊢a* ainstrs0 ∈ [] --> ts3
      -----------------------------------------------------------------
       [(S, C) ⊢a* ainstrs' ∈ [] --> (ts0 ++ ts3)
    *)
    inverts keep HSS;
      try invert_eq_snoc_app H0; 
      try invert_eq_snoc_app H;
      
      apply vais_ts0_ϵ in HVAIS;
      subst ts0; simpl in *;

      remember (length ts1) as n.

    + (* SS_br *)
      rename H2 into Heqn2. 
      (*
        HSS : [Label n instrs0 (plug__B Bl (⇈vals ++ [Plain (Br l0)]))] ↪s ⇈vals ++ ↑instrs0
        ↑instrs0 : ts1 --> ts3
        n = length ts1 = length vals 

        ⇈vals    : [] --> ts1      (* how to connect `C.labels[l] = t*` and `br take vals:t*`?  *)
      ---------------------------------------------------------------------------------------------
        ⇈vals ++ ↑instrs0 : [] --> ts3

      *)
      apply vais_app.
      exists ts1. split...
      (* ⇈vals : [] --> ts1 *)
      admit.

    + (* SS_block__exit *)
      (* we need a context weakening! *)
      admit.


Admitted.

(* Playing with the SC_E proof *)
Theorem preservation : forall S T S' T',
    $(S, T) ↪ $(S', T') ->
    forall rt, ⊢c (S, T) ∈ rt ->
    ⊢c (S', T') ∈ rt /\ ⊢S S ⪯ S'.
Proof with eauto.
  introv HSC.
  destruct T as [F ainstrs].
  destruct T' as [F' ainstrs'].
  simpl in HSC.
  dependent induction HSC; intros.
  - admit.
  -
Abort.    



(* ================================================================= *)
(** ** Lemma - SC_E related... *)


(*
      E[ainstrs] : ts1 --> ts2
   ------------------------------
        ainstrs  : ts3 --> ts4
 *)
Lemma plug_E_inner : forall S C E ainstrs ts1 ts2,
   (S, C) ⊢a* (plug__E E ainstrs) ∈ ts1 --> ts2 ->
   exists ts3 ts4, 
    (S, C) ⊢a* ainstrs ∈ ts3 --> ts4.
Proof with eauto.
  introv HVAIS.
  dependent induction E; simpl in *.
  - (* E_hole *)
    eauto.
  - (* E_seq *)
    apply vais_app3 in HVAIS.
    destruct HVAIS as (ts3 & ts4 & HVAIS0 & HVAIS1 & HVAIS2).
    apply IHE in HVAIS1 as IH.
    destruct IH as (ts3' & ts4' & HVAIS')...
  - (* E_label *)
    inverts HVAIS as HVAIS' HVAI Heq. 
    symmetry in Heq; invert_eq_snoc_app Heq.
    inverts HVAI as HVAIS__cont HVAIS__E.
    (* need context weakening *)
    (* need to reenable VAI_label and it's just two inversions away. *)
    admit.
Admitted.
        

(*
        ainstrs  : ts3 --> ts4
      E[ainstrs] : ts1 --> ts2
        ainstrs' : ts3 --> ts4
   ------------------------------
      E[ainstrs']: ts1 --> ts2
 *)
Lemma plug_E_same : forall S C E ainstrs ainstrs' ts1 ts2 ts3 ts4,
   (S, C) ⊢a* ainstrs ∈ ts3 --> ts4 ->
   (S, C) ⊢a* ainstrs' ∈ ts3 --> ts4 ->
   (S, C) ⊢a* (plug__E E ainstrs) ∈ ts1 --> ts2 ->
   (S, C) ⊢a* (plug__E E ainstrs') ∈ ts1 --> ts2.
Proof with eauto.
  introv Hin Hin' Hplug.
  dependent induction E; simpl in *. 
  - (* E_hole *)
    admit. (* need to show typing is unique *)
  - (* E_seq *)
    apply vais_app3 in Hplug.
    destruct Hplug as (ts3' & ts4' & H0 & H1 & H2).
    apply vais_app3.
    eexists. eexists...
  - (* E_label *)
Admitted.


(*
        ainstrs  :     ts2 --> ts5
      E[ainstrs] : ts1     -->     ts6
        ainstrs' :     ts2 --> ts3
   -------------------------------------
      E[ainstrs']: ts1     -->     ts4
 *)
Lemma plug_E_strong_same : forall S C S' C' E ainstrs ainstrs' ts1 ts3 ts4 ts6,
     (S, C) ⊢a*          ainstrs   ∈ ts3 --> ts4 ->
     (S, C) ⊢a* (plug__E E ainstrs)  ∈ ts1 --> ts6 ->
    (S', C) ⊢a*          ainstrs'  ∈ ts3 --> ts4 ->
    (S', C) ⊢a* (plug__E E ainstrs') ∈ ts1 --> ts6.
Proof with eauto.
  induction E; introv H34 H16 H34'.
  - admit.
  - simpl in *.
    apply vais_app3 in H16 as Happ3.
    destruct Happ3 as (ts2 & ts5 & H12 & H25 & H56). 
    specialize (IHE ainstrs0 ainstrs' ts2 ts3 ts4 ts5 H34 H25 H34') as H25'...
    apply vais_app3.
    exists ts2 ts5. 
    splits. (* Instead, we probably want to show store extension preserve types *)
    + (* vals *) skip.
    + (* hole *) apply H25'.
    + (* rest *) 
      inverts H56 as...
      introv HVAIS56 HVAI__N56.
Admitted.
      
(*
  introv H25 H16 H25'. gen S C S' C'.
  induction E; intros; simpl in *.
  - (* E_hole *)
    admit. (* need to show typing is unique *)
  - (* E_seq *)
    apply vais_app3 in H16 as Happ3.
    destruct Happ3 as (ts3 & ts4 & H23 & H34 & H45). 
    edestruct (IHE ainstrs0 ainstrs'. 
    apply vais_app3.
    eexists. eexists...
  - (* E_label *)
Admitted.
*)

(* ================================================================= *)
(** ** Main Theorem *)

(** Instead of using [remember] to keep infomation from getting lost.

    [dependent induction] (from [Coq.Program.Equality]) or
    [inductions] (from [LibTactics.v]) are used.

    Though w/o [as] the naming is much worse.

    To me dependent induction is like [inversion] + [induction]
*)


(* Generailized Preservation

   The soundness stating in the spec - appendix - soundness was "mis-leading" by being
   too specific to the top-level cases and could not give us a induction hypothesis
   as general as we want to cover all cases.

   So we need a more generalized valid_config (might furthur clean up to a Inductive)
   for now we explicitliy state the premises that required to provide necessary typing
   for us to prove the preservation on the stepped configuration.

   ---------------------------------------------------------------------------

   Some observation in comparsion with original paper and isabelle definition:

   (1) Store

   the paper used so called "store context" which essentially a store typing rule,
   toghther with a store typing weakening rule.

   in the spec setting, we only "valid" a store as "ok" and had a "extending" rule.
   these 2 settings should be effctively equivalent.


 *)
Theorem preservation : forall S F S' F' C ainstrs ainstrs' ts1 ts2,
                  (* valid_config *)
    ⊢S S ok ->       (* valid_store  *) (* valid_thread *)
    S ⊢A F ∈ C ->                         (* valid_frame *)
    (S,C) ⊢a* ainstrs ∈ ts1 --> ts2 ->       (* valid_admin_instr *)
    (S, F, ainstrs) ↪ (S', F', ainstrs') ->  (* step in S_F_ainstrs level *)

(* ---------------------------------------------------------------------------- *)

    ⊢S S ⪯ S' /\    (* weakening *)
      ⊢S S' ok /\      (* valid_store *)
      S' ⊢A F' ∈ C /\  (* valid_frame  *)
      (S',C) ⊢a* ainstrs' ∈ ts1 --> ts2. (* valid_admin_instr *)
Proof with eauto.
  introv HVS HVA HVAIS HSC.
  gen ts1 ts2.
  dependent induction HSC; intros.
  - (* SC_simple *) 
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - (* SC_E *)
    apply plug_E_inner in HVAIS as Hinner.
    destruct Hinner as (ts3 & ts4 & Hinner).
    edestruct (IHHSC ainstrs'0 ainstrs0) as (HES & HVS' & HVA' & Hinner')...
    splits...
    (* only valid_admin_instrs remain, but with different store (up to weakening),
       we need state some a store weakening version of [plug_E_same]
     *)
    Abort.



Theorem preservation : forall S F S' F' C ainstrs ainstrs' ts1 ts2,
                  (* valid_config *)
    ⊢S S ok ->       (* valid_store  *) (* valid_thread *)
    S ⊢A F ∈ C ->                         (* valid_frame *)
    (S,C) ⊢a* ainstrs ∈ ts1 --> ts2 ->       (* valid_admin_instr *)
    (S, F, ainstrs) ↪ (S', F', ainstrs') ->  (* step in S_F_ainstrs level *)

    exists C',
      ⊢S S ⪯ S' /\    (* weakening *)
      ⊢S S' ok /\      (* valid_store *)
      S' ⊢A F' ∈ C' /\  (* valid_frame -- it should be the same C *)
      (S', C') ⊢a* ainstrs' ∈ ts1 --> ts2. (* valid_admin_instr *)
Proof with eauto.
  introv HVS HVA HVAIS HSC.
  gen ts1 ts2.
  dependent induction HSC; intros.
  - (* SC_simple *) 
    exists C.
    inverts HVAIS as.
    + (* VAIS_empty *)
      exfalso.
      eapply (S_F_ϵ_is_normal_form S' _ S' F'). 
      exists ainstrs'...
    + (* VAIS_snoc *)
      introv HVAIS HVAI__N.
      splits... 
         (* valid_frame and valid store immediately follows since no changes for step_simple *)
      ++ (*  ⊢S S' ⪯ S' *)
         apply (extend_store_refl _ HVS).
      ++ (* (S', C) ⊢a* ainstrs' ∈ ts1 --> (ts0 ++ ts4) *)
         (* with a generalized version of [preservation_SC_simple] includes ts1 ... *)
         eapply preservation_SC_simple_gen...

  - (* SC_block *)
    rename H1 into Hlength.
    rename H2 into Hexpand. 
    inverts HVAIS as.
    + (* VAIS_empty *)
      introv Heq; invert_eq_snoc_app Heq.
    + (* VAIS_snoc *)
      introv HVAIS' HVAI__N Heq.

Ltac invert_eq_snoc_app2 Heq :=
  apply eq_snoc_app_split_unsnoc in Heq;
  rewrite unsnoc_snoc_app_some in Heq;
  inverts Heq.

      invert_eq_snoc_app2 Heq. 
      exists C.
      splits...
      ++ apply extend_store_refl...
      ++
        (* 
           The information to connect ts1 with ts is hided in the premises of VI_block,
           so we need to furthur inverts HVAI to the case of VAI_instr.
        *)
          inverts HVAI__N as HVI__block.
          inverts HVI__block as HVBT HVIS__body.

          (* By inversion we destructing the blocktype as well,
             then we can unfold the [expand__F] by simpl.
           *)
          inverts HVBT as; simpl in Hexpand.
          +++ (* VBT_typeidx *)
            introv HCtypes.
            inverts HVA. simpl in Hexpand.
            simpl in HCtypes.
            inverts H.
            simpl in Hexpand.
            (* relation between MI_types and C_types? might involve context weakening again *) 
            skip.
          +++ (* [VBT_valtype__some] => show ts1 is [] *)
            inverts Hexpand.
            skip.
          +++ (* [VBT_valtype__none] => show ts1 and ts4 are [] *)
            inverts Hexpand.
            skip.

  - admit.
  - admit.
  - admit.

  - (* SC_E *)
    apply plug_E_inner in HVAIS as Hinner.
    destruct Hinner as (ts3 & ts4 & Hinner).
    edestruct (IHHSC ainstrs'0 ainstrs0) as (C' & HES & HVS' & HVA' & Hinner')...
    exists C'. splits...
    (* only valid_admin_instrs remain, but with different contexts,
       we need state some context weakening thing that can lead to a stronger [plug_E_same]
     *)
Abort.



(* only top level frame - should be followed as Collary *)
Theorem preservation : forall S T S' T' rt,
    ⊢c (S, T) ∈ rt ->
    $(S, T) ↪ $(S', T') ->
    ⊢c (S', T') ∈ rt /\ ⊢S S ⪯ S'.
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

  introv HSC. simpl in HSC.
    destruct T' as [F' ainstrs'].


  dependent induction HSC.

  - admit.
  - admit.
  - admit.
  - admit.
  - admit.

  - (* SC_E *)
      remember {| A_locals := vals; A_module := mi |} as F.
      remember (C0 with_locals = ts with_return = None) as C.
      (* with [dependent induction], induction hypo is still too specific
         by asking the internal [ainstrs0 ∈ [] --> rt]

         the interesting thing is that with [induction]...
         the induction hypo can immediately prove the goal...!?

         N.B. that [plug__E E ainstrs_whatever] return an ainstrs as well.
         So if the IH is general enough then it can apply back.
         But we lost information by induction generalized like that...
       *)
      eapply IHHSC...
Abort.


Theorem preservation : forall S T S' T' rt,
    ⊢c (S, T) ∈ rt ->
    $(S, T) ↪ $(S', T') ->
    ⊢c (S', T') ∈ rt /\ ⊢S S ⪯ S'.
Proof with eauto.
  introv HVC.

  (* valid_config *)
  inverts HVC as HSok HVT.
    (* valid_store *)
    (* valid_thread *)
    inverts keep HVT as HVA HVAIS.
      (* valid_frame *)
      inverts HVA as HVMI HVV.
        (* valid_moduleinst *)
        (* valid_value *)
      (* valid_admin_instrs *)

  gen S' T'.
  dependent induction HVAIS; 
    introv HSC; simpl in HSC;
    destruct T' as [F' ainstrs'].

  - (* VAIS_empty *)
    exfalso.
    eapply (S_F_ϵ_is_normal_form S _ S' F'). 
    exists ainstrs'...

  - rename H into HVAI__N.
    (* VAIS_snoc:

      [HVAIS : (S,C) ⊢a* ainstrs ∈ ϵ --> (ts0 ++ ts2)]
      [HVAI__N : (S,C) ⊢a  ainstr__N ∈ ts2 --> ts3]              (* H *)
      [HSC   : (S, F, (ainstrs ++ [ainstr__N])) ↪ (S', F', ainstrs')]
       ------------------------------------------------------------
      [⊢c (S', (F', ainstrs')) ∈ rt /\ ⊢S S ⪯ S']

    *)
    clear IHHVAIS.
    dependent induction HSC.

    + (* SC_simple *)
      split. 
      ++ (* Preserve Type *)
          constructor; try apply HSok.
          econstructor; try apply HVA...
          eapply preservation_SC_simple...

      ++ (* Preserve Store *) (* [⊢S S ⪯ S] *)
         apply (extend_store_refl _ HSok). 

    + (* SC_block *) 
      rename x into Heq.
      apply snoc_app_inj in Heq.
      destruct Heq; subst. 
      rename H1 into Hlength.
      rename H2 into Hbt. 
      clear HVT. 
      split. 
      ++ (* Preserve Type *)
          constructor; try apply HSok.
          econstructor; try apply HVA...
          rewrite <- app_nil_l with (l := [Label (length ts4) [] (⇈ vals0 ++ ↑ instrs)]). 

          (* The information is hided in the premises of VI_block,
             so we need to furthur inverts HVAI to the case of VAI_instr.
           *)
          inverts HVAI__N as HVI__block.
          inverts HVI__block as HVBT HVIS__body.

          (* By inversion we destructing the blocktype as well,
             then we can unfold the [expand__F] by simpl.
           *)
          inverts HVBT as; simpl in Hbt.
          +++ (* VBT_typeidx *)
            introv HCtypes.
            (* relation between MI_types and C_types? might involve context weakening again *)
            skip.
          +++ (* [VBT_valtype__some] => show ts1 is [] *)
            inverts Hbt.
            skip.
          +++ (* [VBT_valtype__none] => show ts1 and ts4 are [] *)
            inverts Hbt.
            skip.

      ++ (* Preserve Store *) (* [⊢S S ⪯ S] *)
         apply (extend_store_refl _ HSok). 

    + (* SC_loop *) admit.
    + (* SC_if1 *) admit.
    + (* SC_if2 *) admit.

    + (* SC_E *) 
      (*
         [Heqplug : plug__E E ainstrs0  = ainstrs ++ [ainstr__N]
                =>        E[ainstrs0] = ainstrs ++ ainstrsN
        
         [HSC : (S, F, ainstrs0) ↪ (S', F', ainstrs'0)
       ---------------------------------------------------
          

       *)
      remember {| A_locals := vals; A_module := mi |} as F.
      remember (C0 with_locals = ts with_return = None) as C.
      rename x into Heqplug.
      assert (HVAIS_E : (S,C) ⊢a* (plug__E E ainstrs0) ∈ [] --> (ts0 ++ ts3)).
      { rewrite Heqplug; eapply VAIS_snoc... }
      apply plug_E_inner in HVAIS_E.
      destruct HVAIS_E as (ts03 & ts04 & Hainstrs0).


      (* this induction hypo is not stronger/general enough

           (S', F', ainstrs'0) = (S'0, F'0, ainstrs') ->

         this pose constraints on [ainstrs'0 = ainstrs']
         then this...

           ⊢c (S'0, (F'0, ainstrs')) ∈ ts0 ++ ts3 /\ ⊢S S0 ⪯ S'0

         but ts0 ++ ts3 is the type of [plug__E E ainstrs0] not [ainstrs0]

         but what we want would be

                   [ainstrs0] -(preserve type)-> [       ainstrs0']
           [plug__E E ainstrs0] -(preserve type)-> [plug E ainstrs0']
       *)
(*
Lemma preserve_SC_E_generized: forall S C
*)
                                 

      edestruct IHHSC...
Admitted.

  
   

