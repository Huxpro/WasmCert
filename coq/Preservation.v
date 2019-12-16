(* ***************************************************************** *)
(* Preservation.v                                                    *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)

(* ################################################################# *)
(** * Preservation *)

From Wasm Require Export Validation.
From Wasm Require Export Execution.
From Wasm Require Export ExtendedTyping.
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
(** ** PlugE PlugB **) 

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


(* ================================================================= *)
(** ** Normal Form *)

Definition normal_form {X : Type} (R : relation X) (x : X) : Prop :=
  ~ exists x', R x x'.

(* ----------------------------------------------------------------- *)
(** *** Step simple normal form *)

Lemma ϵ_is_normal_form : 
        normal_form step_simple [].
Proof.
  unfold normal_form. introv. intros H.
  inverts H as. intros ainstrs' HSC.
  inverts HSC.
Qed.

Ltac invert_eq_vals H vals Hnone Hsome :=
  apply eq_unsnoc_car_eq in H; simpl in *;
  specialize (unsnoc_car_vals vals) as [Hnone | Hsome];
    [rewrite -> Hnone in H; inverts H
    | destruct Hsome as [x Hx]; rewrite -> Hx in H; inverts H].

Lemma vals_is_normal_form : forall vals,
    normal_form step_simple (⇈vals).
Proof.
  unfold normal_form. introv. intros H.
  inverts H as. intros ainstrs' HSC.
  inverts HSC; (* will name evidence as H0, H... *)
  (* Drop - no condition, H0 is the Heq *)
  try (rename H0 into H);
  (* Numerics & Select, H0 for some condition, H for the Heq *)
  try (invert_eq_vals H vals Hn Hs).
Qed.

(* To prove this

   destruct vals.
   - []. use S_F_ϵ normal form
   - non-empty. use invert_eq_snoc_app + unsnoc_cons_some
 *)
Lemma S_F_vals_is_normal_form : forall S F vals,
    normal_form step (S, F, ⇈vals).
Proof with auto.
  unfold normal_form. introv. intros H.
  inverts H as. intros ainstrs' HSS.
  inverts HSS;
    try (invert_eq_vals H1 vals Hnone Hsome;
        rewrite unsnoc_car_snoc_app_some in H0; inverts H0);
    try (invert_eq_vals H1 vals Hnone Hsome;
        rewrite unsnoc_car_snoc_app2_some in H0; inverts H0).
  - (* SS_simple *)
    apply (vals_is_normal_form vals).
    exists ainstrs'0...
  - (* SC_E *)
    (* Not easy to show *) admit.
  - (* SC_E__trap *)
    (* easy *) admit.
Admitted.

(* snoc a [val] should be either ill-formed or, normally, all [val] *)
Lemma ainstrs_snoc_app_val_is_normal_form: forall ainstrs val, 
    normal_form step_simple (ainstrs ++ ⇈[val]).
Proof.
  unfold normal_form. introv. intros H.
  inverts H as. intros ainstrs' HSC.
  inverts HSC;
  try invert_eq_snoc_app H;
  try invert_eq_snoc_app H0.
Qed.
      
Lemma instrs_snoc_app_val_normal_form: forall instrs val, 
    normal_form step_simple (↑(instrs ++ [Const val])).
Proof.
  intros.
  specialize (map_app Plain instrs [Const val]). intros.
  rewrite H.
  apply ainstrs_snoc_app_val_is_normal_form.
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
(** ** Preservation - SC_simple *)


(* ----------------------------------------------------------------- *)
(** *** Preservation - SC_simple VAI_instr *)

Lemma preservation_SC_simple_VAI_instr : forall S C ainstrs ainstrs' instr ts0 ts1 ts2 ts3, 
    (S, C) ⊢a* ainstrs ∈ ts1 --> (ts0 ++ ts2) -> (* [HVAIS] *)
    C ⊢ instr ∈ ts2 --> ts3 ->                   (* [HVI__N] *)
    ainstrs ++ ↑[instr] ↪s ainstrs' ->          (* [HSS] *)
    (* ------------------------------------------------------------------- *)
    (S, C) ⊢a* ainstrs' ∈ ts1 --> (ts0 ++ ts3).
Proof with eauto.
  introv HVAIS HVI__N HSS.
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
        apply vais_vals with (vals := [val1]) in HVAIS; simpl in HVAIS.
        apply snoc_app_inj in HVAIS; destruct HVAIS as (Heqts0 & Htypeof).
        subst; rewrite app_nil_r. constructor.

      +++ (* ↑[Const val] *)
        apply VAI_instr.
        apply VI_const.
        apply eval_unop_preserve_type in Heval...

    ++ (* [SS_unop__none] *)
      rewrite <- (app_nil_l ([Trap])).
      apply VAIS_snoc with (ts := []). 

      +++ (* [] *)
        apply vais_vals with (vals := [val1]) in HVAIS; simpl in HVAIS.
        apply snoc_app_inj in HVAIS; destruct HVAIS as (Heqts0 & Htypeof).
        subst; rewrite app_nil_r. constructor.

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
        apply vais_vals with (vals := [val1; val2]) in HVAIS; simpl in HVAIS.
        destruct (app_eq_same_len ts0 ts1 [type_of op; type_of op] [type_of val1; type_of val2])... 
        subst; rewrite app_nil_r. constructor.


      +++ (* ↑[Const val] *)
        apply VAI_instr.
        apply VI_const.
        apply eval_binop_preserve_type in Heval...

    ++ (* [SS_binop__none] *)
      rewrite <- (app_nil_l ([Trap])).
      apply VAIS_snoc with (ts := []). (* We know [ts] from [Const val]*)

      +++ (* [] *)
        apply vais_vals with (vals := [val1; val2]) in HVAIS; simpl in HVAIS.
        destruct (app_eq_same_len ts0 ts1 [type_of op; type_of op] [type_of val1; type_of val2])... 
        subst; rewrite app_nil_r. constructor.

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
        apply vais_vals with (vals := [val1]) in HVAIS; simpl in HVAIS.
        destruct (app_eq_same_len ts0 ts1 [type_of op] [type_of val1])... 
        subst; rewrite app_nil_r. constructor.

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
        apply vais_vals with (vals := [val1; val2]) in HVAIS; simpl in HVAIS.
        destruct (app_eq_same_len ts0 ts1 [type_of op; type_of op] [type_of val1; type_of val2])... 
        subst; rewrite app_nil_r. constructor.

      +++ (* ↑[Const b] *)
        apply VAI_instr.
        apply VI_const.
        simpl...  (* no need for eval_relop_preserve_type... *)

  + (* VI_drop *)
    inverts keep HSS; 
      try invert_eq_snoc_app H0;
      try invert_eq_snoc_app H.

    ++ (* [SS_drop] *)
      apply vais_vals with (vals := [val]) in HVAIS; simpl in HVAIS.
      destruct (app_eq_same_len ts0 ts1 [t] [type_of val])... 
      subst; rewrite app_nil_r. constructor.


  + (* VI_select *)
    inverts keep HSS; 
      try invert_eq_snoc_app H0;
      try invert_eq_snoc_app H.

    ++ (* [SS_select1] *)
      rewrite <- (app_nil_l (↑[Const val1])).
      apply VAIS_snoc with (ts := []);

        apply vais_vals with (vals := [val1; val2; (i32 c)]) in HVAIS; simpl in HVAIS;
        destruct (app_eq_same_len ts0 ts1 [t; t; T_i32] [type_of val1; type_of val2; T_i32])... 

      +++ (* [] *)
        subst; rewrite app_nil_r. constructor.

      +++ (* ↑[Const val1] *)
        inverts H1.
        apply VAI_instr.
        apply VI_const.
        simpl... 

    ++ (* [SS_select2] *)
      rewrite <- (app_nil_l (↑[Const val2])).
      apply VAIS_snoc with (ts := []);

        apply vais_vals with (vals := [val1; val2; (i32 c)]) in HVAIS; simpl in HVAIS;
        destruct (app_eq_same_len ts0 ts1 [t; t; T_i32] [type_of val1; type_of val2; T_i32])... 

      +++ (* [] *)
        subst; rewrite app_nil_r. constructor.

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

    inverts HVAIS.
    ++ (* [] *)
      rewrite <- (app_nil_l ([Trap])).
      apply VAIS_snoc with (ts := ts2)... (* Interesting... *)
    ++ (* [] *)
      symmetry in H1.
      invert_eq_snoc_app H1.


  + (* VI_br_if *)
    intros Hl0.
    inverts keep HSS; 
      try invert_eq_snoc_app H0;
      try invert_eq_snoc_app H;

        apply vais_vals with (vals := [(i32 c)]) in HVAIS; simpl in HVAIS;
        rewrite app_assoc in HVAIS;
        destruct (app_eq_same_len (ts0++ts3) ts1 [T_i32] [T_i32]); eauto; subst.

    ++ (* [SS_br_if1 ↪ br] *)
      rewrite <- (app_nil_l (↑[Br l0])).
      eapply VAIS_snoc... (* Br take the labels type [ts3], but the [eauto] is smart enough *)
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
        apply vais_vals with (vals := [(i32 c)]) in HVAIS; simpl in HVAIS;
        rewrite app_assoc in HVAIS; rewrite app_assoc in HVAIS;
          destruct (app_eq_same_len ((ts0 ++ ts4) ++ ts) ts1 [T_i32] [T_i32]);
          eauto; subst;
            rewrite <- app_assoc.  (* So that eapply can find the unification in nil case *)

    ++ (* [SS_br_table__i] *)
      rewrite <- (app_nil_l (↑[Br l__i])).
      eapply VAIS_snoc...
      +++ (* [Br l__i] *)
        eapply VAI_instr.
        eapply VI_br... (* with (ts1 := ts4) *)
        eapply Forall_forall with (x := l__i) in Hls...
        eapply nth_error_In...

    ++ (* [SS_br_table__N] *)
      rewrite <- (app_nil_l (↑[Br l__N])).
      eapply VAIS_snoc... 
Qed.


(* ----------------------------------------------------------------- *)
(** *** Preservation - SC_simple VAI_label *)

(* If we cons a new label, then the same label need to be lookuped one step deeper. *)
Lemma Clabels_cons : forall C ts1 ts2 n,
   C            .(C_labels).[n    ] = Some ts2 ->
  (C,labels ts1).(C_labels).[n + 1] = Some ts2.    
Proof with auto.
  introv Hn; simpl in *.
  rewrite cons_to_app.
  rewrite nth_error_app2; simpl; try omega.
  asserts_rewrite (n + 1 - 1 = n); try omega...
Qed. 

Lemma Clabels_cons_sub : forall C ts1 ts2 n,
   n >= 1 ->
   C            .(C_labels).[n - 1] = Some ts2 ->
  (C,labels ts1).(C_labels).[n    ] = Some ts2.    
Proof with auto.
  introv Hgt H.
  apply Clabels_cons with (ts1 := ts1) (n := n - 1) in H.
  asserts_rewrite (n - 1 + 1 = n) in H; try omega...
Qed.


(*
Single-step:
           
  C.#l+1   C.#l 
  B^{l+1}  B^{l}        B^{l-1}
  B       [
           label {cont} [
           ↑             label {cont'} [vals; br l] ] ]  ↪ vals; cont
           |                                     |
           |________________________ ____________|
                                                

Generalized:

  C.#l     C.#l' 
  B^{l}    B^{l'}
  label...[
           label {cont} [...
           ↑                           [vals; br l] ... ↪ vals; cont
           |                                     |
           |________________________ ____________|
    
*)

Lemma Bl_give_vals : forall S C l (Bl: block_context l) l' vals ts3 ts4,
   l' >= l ->
   (S, C) ⊢a* plug__B Bl (⇈ vals ++ ↑[Br l']) ∈ [] --> ts3 -> 
   C.(C_labels).[l' - l] = Some ts4 ->
   length vals = length ts4 ->
(* ----------------------------------------------------------- *)
   (S, C) ⊢a* ⇈ vals ∈ [] --> ts4.
Proof with eauto.
  introv Hgt HVAIS HClabels Heqlen.
  gen C ts3 ts4 vals.
  induction Bl;
  introv HClabels HVAIS Heqlen.

  - (* B_nil, [Br 0], only one Label wrapped *)
(*
  [HVAIS__body: (S, C,labels ts4) ⊢a* ⇈vals0 ++ (⇈vals ++ ↑[Br 0]) ++ ainstrs ∈ [] --> ts3
*)
    simpl in HVAIS.
    rewrite app_assoc in HVAIS.
    apply vais_app in HVAIS.
    destruct HVAIS as (ts2 & HVAIS__br & HVAIS__rest).  (* split *)

(*
  [HVAIS__br : (S, C,labels ts4) ⊢a* ⇈ vals0 ++ ⇈ vals ++ ↑[Br 0] ∈ [] --> ts2

  we show [br] took [length ts4] of [val] before it, which happened to be [vals] thus [ts2 = ts4].
  we prove that by invert [HVAIS__br] to [HVAI__br] to [HVI__br] to [HClabels] lookup.
*)
    rewrite app_assoc in HVAIS__br.
    inverts HVAIS__br as;
      try (intros Heq; invert_eq_snoc_app Heq).
    
    introv HVAIS__vals HVAI__br Heq. 
    invert_snoc_app_eq_snoc_app Heq.

    inverts HVAI__br as HVI__br.
    inverts keep HVI__br as HClabels'.

(* we proved [ts1 = ts4] *)
    rewrite Nat.sub_0_r in HClabels.
    rewrite HClabels in HClabels'.
    invert HClabels' as Htseq; subst ts1.
(*
  [HVAIS__vals : (S, C,labels ts4) ⊢a* ⇈ vals0 ++ ⇈ vals ∈ [] --> (ts0 ++ ts2 ++ ts4)

  We then show that [length vals = length ts4 = n] and split [vals ∈ ts4] then close the proof.
*)
    rewrite app_assoc in HVAIS__vals.
    specialize (vais_vals_len_app_r _ _ _ _ _ _ _ Heqlen HVAIS__vals) as HVAIS__valsts4.
    rewrite app_nil_l in HVAIS__valsts4...

  - (* B_cons, [Br k + 1], k + 1 Labels *)
    simpl in *. (* so we can reveal the sub-structure *)
    rewrite cons_to_app in HVAIS.
    rename k into l.
(*

[Bl: block_context l     <--- general k
[HClabels : C.(C_labels)[ l' - (l + 1)] = Some ts4
[HVAIS: (S, C) ⊢a*
  ⇈ vals ++ [Label n cont (plug__B Bl (⇈ vals0 ++ ↑[Br l']))] ++ ainstrs  ∈ [] --> ts3

                                length vals0 = length ts4
------------------------------------------------------------------------------------------ 
                                      ⇈vals0             ∈ []  --> ts4      

*)
    rewrite app_assoc in HVAIS.
    apply vais_app in HVAIS.
    destruct HVAIS as (ts2 & HVAIS__label & HVAIS__rest).  (* split *)
(*

[HClabels : C.(C_labels)[ l' - (l + 1)] = Some ts4
[HVAIS__label : (S, C) ⊢a* ⇈ vals0 ++ [Label n cont (plug__B Bl (⇈ vals ++ ↑[Br l']))] ∈ [] --> ts2

  we want to show that [br] took [length ts4] of [val] before it, which happened to be [vals].
  but we will encounter sub-structure [Bl] which will use the IH.
*)
    inverts HVAIS__label as;
      try (intros Heq; invert_eq_snoc_app Heq).
    introv HVAIS__vals HVAI__label Heq. 
    invert_snoc_app_eq_snoc_app Heq.
    inverts HVAI__label as HVAIS__cont' HVAIS'.
(*
[HVAIS': (S, C,labels ts1) ⊢a* plug__B Bl (⇈ vals0 ++ [Plain (Br l')]) ∈ [] --> ts5
*)

(*
We wanna show: 
  l' > l
  C_labels  C             .[ l' - (l + 1)] = Some ts4
  -----------------------------------------------------
  C_labels (C,labels ts1) .[ l' - l      ] = Some ts4

Which naturally ask for a lemma:
*)

    rewrite Nat.sub_add_distr in HClabels. 
    apply Clabels_cons_sub with (ts1 := ts1) in HClabels as HClabels'; try omega.
    assert (Hgt': l' >= l); try omega.
    specialize (IHBl Hgt' (C,labels ts1) ts5 ts4 HClabels' vals0 HVAIS' Heqlen) as Hvals.
    eapply vais_vals_SC_weakening in Hvals...
Qed.    


Lemma preservation_SC_simple_VAI_label : forall S C ainstrs ainstrs' ainstrs0 ainstrs1 ts0 ts1 ts3 ts4,
    (S, C) ⊢a* ainstrs ∈ ts1 --> ts0 ->            (* [HVAIS] *)
    (S, C) ⊢a* ainstrs0 ∈ ts4 --> ts3 ->           (* [HVAIS__cont] *) 
    (S, C,labels ts4) ⊢a* ainstrs1 ∈ [] --> ts3 ->  (* [HVAIS__body] *) 
    ainstrs ++ [Label (length ts4) ainstrs0 ainstrs1] ↪s ainstrs' -> (* [HSS] *)
    (* ------------------------------------------------------------------- *)
    (S, C) ⊢a* ainstrs' ∈ ts1 --> (ts0 ++ ts3).
Proof with eauto.
  introv HVAIS HVAIS__cont HVAIS__body HSS.

  inverts keep HSS;
    try invert_eq_snoc_app H0; 
    try invert_eq_snoc_app H;

    (* Because it's [step_simple], the [ainstr] before [Label] is always [ϵ] *)
    inverts HVAIS;
    try invert_eq_snoc_app_sym H1. 

  + (* [SS_br] *) 
    rewrite app_nil_l in HSS.

(*
    [Label n instrs0 (plug__B Bl (⇈vals ++ ↑[Br l0]))] ↪s ⇈vals ++ ↑instrs0  (* HSS *) 

    length ts4 = length vals = n
    ---------------------------------------------------------------- Bl_give_vals
    ⇈vals             : []  --> ts4           

             ↑instrs0 :         ts4 --> ts3   (we already have)
    ----------------------------------------------------------------- goal, by [vais_app]
    ⇈vals ++ ↑instrs0 : ts0 --> (ts0 ++ ts3)


    [HSS] told us we are in the case of [br l0]-ing out of [Bl : block_context l0],
    taking a polymorphic (arbitrary) [ts1] and some [vals] typed as the current labels [ts],
    so the contiuation part can safely typed [ts --> ?] and continue the execution with [vals]

    By inverting the typing [HAVIS__body] somehow we should be able to use [VAI_label]
    to show that those [vals] are actually typed [ts4] (same as the labels)
*)
  
    assert (Hvals : (S, C,labels ts4) ⊢a* ⇈ vals ∈ [] --> ts4).
    apply (Bl_give_vals S (C,labels ts4) l0 Bl l0 vals ts3 ts4)...
    rewrite Nat.sub_diag...

    apply vais_app. 
    exists (ts0 ++ ts4); split...
    eapply vais_vals_SC_weakening.
    apply vais_weakening with (ts0 := ts0)...
    apply vais_weakening_app with (ts0 := ts0)...

  + (* [SS_block__exit] *)
    eapply vais_vals_SC_weakening.
    apply vais_weakening with (ts0 := ts0)...
Qed.    



Lemma preservation_SC_simple_VAIS_snoc : forall S C ainstrs ainstr__N ainstrs' ts0 ts1 ts2 ts3,
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
    eapply preservation_SC_simple_VAI_instr...

  - (* VAI_trap *)
    inverts keep HSS;
      try invert_eq_snoc_app H0; 
      try invert_eq_snoc_app H.

  - (* VAI_label *)
    introv HVAIS__cont HVAIS__body.
    (* [Label] take no input types, thus the "bridge type" [ts] is `[]` *)
    rewrite app_nil_r in HVAIS.
    eapply preservation_SC_simple_VAI_label...
Qed.

Lemma preservation_SC_simple: forall C S F ainstrs ainstrs' ts1 ts2,
    ⊢S S ok ->      (* HVS *)
    S ⊢A F ∈ C ->   (* HVA *)
    (S, C) ⊢a* ainstrs ∈ ts1 --> ts2 -> (* HVAIS *)
    ainstrs ↪s ainstrs' -> (* HSS *)
(* -------------------------------------------- *)
    (S, C) ⊢a* ainstrs' ∈ ts1 --> ts2.
Proof with eauto.
  introv HVS HVA HVAIS HSS.
  inverts HVAIS.
  - (* VAIS_empty *)
    exfalso. apply ϵ_is_normal_form.
    exists ainstrs'...
  - (* VAIS_snoc *)
    eapply preservation_SC_simple_VAIS_snoc...
Qed.



(* ================================================================= *)
(** ** Preservation - SC_block *)

(* By using this lemma,
   We can hide the [locals] inverted from [frame] and made proof cleaner.
*)
Lemma vbt_expand : forall S C F bt ts1 ts2 ts3 ts4,
  S ⊢A F ∈ C ->
  expand F bt = Some (ts1 --> ts2) -> (* Hexpand *)
  C ⊢bt bt ∈ ts3 --> ts4 -> (*  HVBT *)
  (ts1 --> ts2) = (ts3 --> ts4).
Proof with eauto.
  introv HVA Hexpand HVBT.
  inverts HVBT as; simpl in Hexpand.

  - (* VBT_typeidx *)
    introv HCtypes.

(* In the [BT_typeidx] case we look up the types from context [C] and moduleinst in the [F']

[ HCtypes : C_types C .[ i] = Some (ts --> ts6)
[ HVA : S' ⊢A F' ∈ C
[ Hexpand : MI_types (A_module F') .[ i] = Some (ts1 --> ts2)

Inverts [HVA] here will give us the closed moduleinst [mi] and let us furthur simpl.
also some locals [val0 : ts3] and [C with_locals = ts3] from frame [F], but nouse here.
*)

    inverts HVA as HVMI HVVS.
    simpl in Hexpand.
    simpl in HCtypes.

(*

[ HCtypes : C_types C0 .[ i] = Some (ts --> ts6)
[ Hexpand : MI_types mi .[ i] = Some (ts1 --> ts2)
[ HVMI : S' ⊢mi mi ∈ C0

Inverts on [HMI] here will give us the members of [mi] where [ MI_types = C.(C_types) ]
*)
    inverts HVMI as HVFTS.
    simpl in *.
    rewrite HCtypes in Hexpand. 
    inverts Hexpand...
   
  - (* [VBT_valtype__some] *)
    inverts Hexpand...

  - (* [VBT_valtype__none] *)
    inverts Hexpand...
Qed.

Lemma preservation_SC_block: forall S F C vals instrs bt ts0 ts1 ts2 ts3,
                   (* HSS is gone... *)
    ⊢S S ok ->      (* HVS *)
    S ⊢A F ∈ C ->   (* HVA *)
    length vals = length ts1 -> (* Hlength *)
    expand F bt = Some (ts1 --> ts2) -> (* Hexpand *)
    (S, C) ⊢a* ⇈ vals ++ ↑[Block bt instrs] ∈ ts0 --> ts3 -> (* HVAIS *)
(* --------------------------------------------------------------------------*)
    (S, C) ⊢a* [Label (length ts2) [] (⇈ vals ++ ↑ instrs)] ∈ ts0 --> ts3.
Proof with eauto.
  introv HVS HVA Hlength Hexpand HVAIS.
  inverts HVAIS as.

  - (* VAIS_empty *)
    introv Heq; invert_eq_snoc_app Heq.
  - (* VAIS_snoc *)
    introv HVAIS' HVAI__N Heq.
    invert_snoc_app_eq_snoc_app Heq. 
    
    inverts HVAI__N as HVI__block.
    inverts keep HVI__block as HVBT HVIS__body.

(* after inversion on VI_block, we have [HVBT] to connect with [Hexpand]

[ HVBT :     C ⊢bt bt ∈ ts --> ts6
[ Hexpand : expand F' bt = Some (ts1 --> ts2)

  our goal is to eventually prove [(ts --> ts6) = (ts1 --> ts2)],
  thus connect the

  - continuation part (in this case is ϵ)
  - and body part: [C,labels ts6 ⊢* body ∈ ts --> ts6] 

   and eventuall give us the type preservation on [Label (length ts2) body... ∈ --> ts2]
*)

    specialize (vbt_expand _ _ _ _ _ _ _ _ HVA Hexpand HVBT) as Hbt.
    inverts keep HVBT as; inverts Hbt; simpl in Hexpand. 

    + (* VBT_typeidx *)
      introv HCtypes.

(* 
[ Hlength : length vals = length ts
[ HVAIS' : (S, C) ⊢a* ⇈ vals ∈ ts0 --> (ts4 ++ ts)
From this pair we can show [ts0 = ts4].
*)
      specialize (vais_vals_len _ _ _ _ _ _ Hlength HVAIS') as Htseq;
        subst ts4.
      
(*

[                             ∀C ⊢a* ⇈vals ∈ ts0 --> (ts0 ++ ts)          + weakening
[                                C,labels ts6  ⊢* instrs  ∈ ts --> ts6   + lifting
------------------------------------------------------------------------------------- VAIS_app
[                  C,labels ts6  ⊢a* (⇈ vals ++ ↑ instrs)  ∈ [] --> ts6
-------------------------------------------------------------------------------------- VAI_label
[        C ⊢a [Label (length ts6) [] (⇈ vals ++ ↑ instrs)] ∈ [] --> ts6
--------------------------------------------------------------------------------------- VAIS_snoc
[ C ⊢a* [] ++ [Label (length ts6) [] (⇈ vals ++ ↑ instrs)] ∈ ts0 --> (ts0 ++ ts6)
*)
      apply vais_ainstrs_app_nil_l. 
      eapply VAIS_snoc with (ts := []);
        try rewrite app_nil_r...
      (* ⊢a *) eapply VAI_label...

      eapply vais_app.
      exists ts; split.
      eapply vais_weakening...
      eapply vais_vals_SC_weakening...
      apply vis_to_vais...

    + (* [VBT_valtype__some] *)
      inverts Hexpand. simpl in Hlength.
      apply length_zero_iff_nil in Hlength; subst vals.
      rewrite app_nil_l.
      inverts HVAIS';
        try (symmetry in H1; invert_eq_snoc_app H1). (* can only be [] case *)
      apply vais_ainstrs_app_nil_l. 
      eapply VAIS_snoc with (ts := [])...
      (* ⊢a *)
      eapply VAI_label...
      eapply vis_to_vais...

    + (* [VBT_valtype__none] *)
      inverts Hexpand. simpl in Hlength.
      apply length_zero_iff_nil in Hlength; subst vals.
      rewrite app_nil_l.
      inverts HVAIS';
        try (symmetry in H1; invert_eq_snoc_app H1). (* can only be [] *)
      apply vais_ainstrs_app_nil_l. 
      eapply VAIS_snoc with (ts := [])...
      (* ⊢a *)
      eapply VAI_label...
      apply vis_to_vais...
Qed.


(* ================================================================= *)
(** ** Preservation - SC_loop *)

Lemma preservation_SC_loop: forall S F C vals instrs bt ts0 ts1 ts2 ts3,
                   (* HSS is gone... *)
    ⊢S S ok ->      (* HVS *)
    S ⊢A F ∈ C ->   (* HVA *)
    length vals = length ts1 -> (* Hlength *)
    expand F bt = Some (ts1 --> ts2) -> (* Hexpand *)
    (S, C) ⊢a* ⇈vals ++ ↑[Loop bt instrs] ∈ ts0 --> ts3 -> (* HVAIS *)
(* -------------------------------------------------------------------------------------------- *)
    (S, C) ⊢a* [Label (length ts1) ↑[Loop bt instrs] (⇈vals ++ ↑instrs)] ∈ ts0 --> ts3.
Proof with eauto.
  introv HVS HVA Hlength Hexpand HVAIS.
  inverts HVAIS as.

  - (* VAIS_empty *)
    introv Heq; invert_eq_snoc_app Heq.

  - (* VAIS_snoc *)
    introv HVAIS' HVAI__N Heq.
    invert_snoc_app_eq_snoc_app Heq. 
    
    inverts HVAI__N as HVI__loop.
    inverts HVI__loop as HVBT HVIS__body.

(* after inversion on VI_loop, we have [HVBT] to connect with [Hexpand]

[ HVBT :     C ⊢bt bt ∈ ts --> ts6
[ Hexpand : expand F' bt = Some (ts1 --> ts2)

  our goal is to eventually prove [(ts --> ts6) = (ts1 --> ts2)],
  thus connect the

  - continuation part
  - and body part: [C,labels ts6 ⊢* body ∈ ts --> ts6] 

  and eventuall give us the type preservation on [Label (length ts1) body... ∈ --> ts2]
*)
    specialize (vbt_expand _ _ _ _ _ _ _ _ HVA Hexpand HVBT) as Hbt.
    inverts keep HVBT as; inverts Hbt; simpl in Hexpand. 

    + (* VBT_typeidx *)
      introv HCtypes.
      specialize (vais_vals_len _ _ _ _ _ _ Hlength HVAIS') as Htseq;
        subst ts4.

(*
(HVBT) : C ⊢bt BT_typeidx i ∈ ts --> ts6

(Body):
[                           ∀C ⊢a* ⇈vals ∈ ts0 --> (ts0 ++ ts)       + weakening
[                             C,labels ts  ⊢* instrs  ∈ ts --> ts6   + lifting
------------------------------------------------------------------------------------- VAIS_app
[                  C,labels ts ⊢a* (⇈vals ++ ↑instrs) ∈ [] --> ts6


(Cont):
[                    C ⊢bt bt (BT_typeidx i)          ∈ ts --> ts6
[                              C,labels ts ⊢* instrs  ∈ ts --> ts6
------------------------------------------------------------------------------------ VI_loop
[                    C ⊢ (Loop (BT_typeidx i) instrs) ∈ ts --> ts6
                   [] ∈ ts --> ([] ++ ts)
------------------------------------------------------------------------------------- VAIS_snoc
[      (S, C) ⊢a* [] ++ ↑[Loop (BT_typeidx i) instrs] ∈ ts --> [] ++ ts6
[      (S, C) ⊢a* [] ++ ↑[Loop (BT_typeidx i) instrs] ∈ ts --> ts6


                                  (Cont) (      Body      )
-------------------------------------------------------------------------------------- VAI_label
[        C ⊢a [Label (length ts) ↑[Loop] (⇈vals ++ ↑instrs)] ∈ [] --> ts6
--------------------------------------------------------------------------------------- VAIS_snoc
[ C ⊢a* [] ++ [Label (length ts) ↑[Loop] (⇈vals ++ ↑instrs)] ∈ ts0 --> (ts0 ++ ts6)
*)
      apply vais_ainstrs_app_nil_l. 
      eapply VAIS_snoc with (ts := []);
        try rewrite app_nil_r...

      eapply VAI_label... 
      ++ (* Cont *)
        apply vais_ainstrs_app_nil_l. 
        apply vais_ts_app_nil_l. 
        eapply VAIS_snoc with (ts := ts)...
      ++ (* Body *)
        eapply vais_app.
        exists ts; split.
        eapply vais_weakening...
        eapply vais_vals_SC_weakening...
        eapply vis_to_vais...

    + (* [VBT_valtype__some] *)
      inverts Hexpand. simpl in Hlength.
      apply length_zero_iff_nil in Hlength; subst vals.
      rewrite app_nil_l.
      inverts HVAIS';
        try (symmetry in H1; invert_eq_snoc_app H1). (* can only be [] case *)
      apply vais_ainstrs_app_nil_l. 
      eapply VAIS_snoc with (ts := [])...
      (* ⊢a *)
      eapply VAI_label...
      ++ (* Cont *)
        apply vais_ainstrs_app_nil_l. 
        apply vais_ts_app_nil_l. 
        eapply VAIS_snoc...
        rewrite app_nil_l...
      ++ (* Body *)
        apply vis_to_vais...

    + (* [VBT_valtype__none] *)
      inverts Hexpand. simpl in Hlength.
      apply length_zero_iff_nil in Hlength; subst vals.
      rewrite app_nil_l.
      inverts HVAIS';
        try (symmetry in H1; invert_eq_snoc_app H1). (* can only be [] *)
      apply vais_ainstrs_app_nil_l. 
      eapply VAIS_snoc with (ts := [])...
      (* ⊢a *)
      eapply VAI_label...
      ++ (* Cont *)
        apply vais_ainstrs_app_nil_l. 
        apply vais_ts_app_nil_l. 
        eapply VAIS_snoc...
        rewrite app_nil_l...
      ++ (* Body *)
        apply vis_to_vais...
Qed.

(* ================================================================= *)
(** ** Preservation - [SC_if__nez] *)

Lemma preservation_SC_if__nez: forall S F C vals instrs1 instrs2 bt ts0 ts1 ts2 ts3 (c: I32.t),
                   (* HSS is gone... *)
    ⊢S S ok ->      (* HVS *)
    S ⊢A F ∈ C ->   (* HVA *)
    length vals = length ts1 -> (* Hlength *)
    expand F bt = Some (ts1 --> ts2) -> (* Hexpand *)
    (S, C) ⊢a* ⇈vals ++ ↑[(Const (i32 c)); (If bt instrs1 instrs2)] ∈ ts0 --> ts3 -> (* HVAIS *)
(* ------------------------------------------------------------------------------------------*)
    (S, C) ⊢a* [Label (length ts2) [] (⇈vals ++ ↑instrs1)] ∈ ts0 --> ts3.
Proof with eauto.
  introv HVS HVA Hlength Hexpand HVAIS.
  inverts HVAIS as.

  - (* VAIS_empty *)
    introv Heq; rewrite snoc_app2_as_snoc_app in Heq; invert_eq_snoc_app Heq.

  - (* VAIS_snoc *)
    introv HVAIS' HVAI__N Heq.
    rewrite snoc_app2_as_snoc_app in Heq; 
      invert_snoc_app_eq_snoc_app Heq. 
    
    inverts HVAI__N as HVI__if.
    inverts keep HVI__if as HVBT HVIS1 HVIS2.

    specialize (vbt_expand _ _ _ _ _ _ _ _ HVA Hexpand HVBT) as Hbt.
    inverts keep HVBT as; inverts Hbt; simpl in Hexpand. 

    + (* VBT_typeidx *)
      introv HCtypes.

      destruct (vais_vals_len_app S C vals [(i32 c)] ts0 ts4 ts3 [T_i32])
        as (Hts0 & HVAIS__vals1 & HVAIS__vals2)...
      subst ts4.
      apply vais_ainstrs_app_nil_l. 
      eapply VAIS_snoc with (ts := []);
        try rewrite app_nil_r...
      (* ⊢a *)
      eapply VAI_label...
      apply vais_app. exists ts3; split...
      eapply vais_vals_SC_weakening...
      apply vis_to_vais...

    + (* [VBT_valtype__some] *)
      inverts Hexpand. simpl in Hlength.
      apply length_zero_iff_nil in Hlength; subst vals.
      rewrite app_nil_l.

      (* different in how to handle [HVAIS'] and get [ts0 = ts4] here *)
      rewrite app_nil_l in HVAIS'.
      rewrite app_nil_l in HVAIS'.
      destruct (vais_vals_len S C [(i32 c)] ts0 ts4 [T_i32])...

      apply vais_ainstrs_app_nil_l. 
      eapply VAIS_snoc with (ts := []);
        try rewrite app_nil_r...
      (* ⊢a *)
      eapply VAI_label...
      eapply vis_to_vais...

    + (* [VBT_valtype__none] *)
      inverts Hexpand. simpl in Hlength.
      apply length_zero_iff_nil in Hlength; subst vals.
      rewrite app_nil_l.

      (* different in how to handle [HVAIS'] and get [ts0 = ts4] here *)
      rewrite app_nil_l in HVAIS'.
      rewrite app_nil_l in HVAIS'.
      destruct (vais_vals_len S C [(i32 c)] ts0 ts4 [T_i32])...

      apply vais_ainstrs_app_nil_l. 
      eapply VAIS_snoc with (ts := []);
        try rewrite app_nil_r...
      (* ⊢a *)
      eapply VAI_label...
      apply vis_to_vais...
Qed.

(* ================================================================= *)
(** ** Preservation - [SC_if__eqz] *)

Lemma preservation_SC_if__eqz: forall S F C vals instrs1 instrs2 bt ts0 ts1 ts2 ts3 (c: I32.t),
                   (* HSS is gone... *)
    ⊢S S ok ->      (* HVS *)
    S ⊢A F ∈ C ->   (* HVA *)
    length vals = length ts1 -> (* Hlength *)
    expand F bt = Some (ts1 --> ts2) -> (* Hexpand *)
    (S, C) ⊢a* ⇈vals ++ ↑[(Const (i32 c)); (If bt instrs1 instrs2)] ∈ ts0 --> ts3 -> (* HVAIS *)
(* ------------------------------------------------------------------------------------------*)
    (S, C) ⊢a* [Label (length ts2) [] (⇈vals ++ ↑instrs2)] ∈ ts0 --> ts3.
Proof with eauto.
  introv HVS HVA Hlength Hexpand HVAIS.
  inverts HVAIS as.

  - (* VAIS_empty *)
    introv Heq; rewrite snoc_app2_as_snoc_app in Heq; invert_eq_snoc_app Heq.

  - (* VAIS_snoc *)
    introv HVAIS' HVAI__N Heq.
    rewrite snoc_app2_as_snoc_app in Heq; 
      invert_snoc_app_eq_snoc_app Heq. 
    
    inverts HVAI__N as HVI__if.
    inverts keep HVI__if as HVBT HVIS1 HVIS2.

    specialize (vbt_expand _ _ _ _ _ _ _ _ HVA Hexpand HVBT) as Hbt.
    inverts keep HVBT as; inverts Hbt; simpl in Hexpand. 

    + (* VBT_typeidx *)
      introv HCtypes.

      destruct (vais_vals_len_app S C vals [(i32 c)] ts0 ts4 ts3 [T_i32])
        as (Hts0 & HVAIS__vals1 & HVAIS__vals2)...
      subst ts4.
      apply vais_ainstrs_app_nil_l. 
      eapply VAIS_snoc with (ts := []);
        try rewrite app_nil_r...
      (* ⊢a *)
      eapply VAI_label...
      apply vais_app. exists ts3; split...
      eapply vais_vals_SC_weakening...
      apply vis_to_vais...

    + (* [VBT_valtype__some] *)
      inverts Hexpand. simpl in Hlength.
      apply length_zero_iff_nil in Hlength; subst vals.
      rewrite app_nil_l.

      (* different in how to handle [HVAIS'] and get [ts0 = ts4] here *)
      rewrite app_nil_l in HVAIS'.
      rewrite app_nil_l in HVAIS'.
      destruct (vais_vals_len S C [(i32 c)] ts0 ts4 [T_i32])...

      apply vais_ainstrs_app_nil_l. 
      eapply VAIS_snoc with (ts := []);
        try rewrite app_nil_r...
      (* ⊢a *)
      eapply VAI_label...
      eapply vis_to_vais...

    + (* [VBT_valtype__none] *)
      inverts Hexpand. simpl in Hlength.
      apply length_zero_iff_nil in Hlength; subst vals.
      rewrite app_nil_l.

      (* different in how to handle [HVAIS'] and get [ts0 = ts4] here *)
      rewrite app_nil_l in HVAIS'.
      rewrite app_nil_l in HVAIS'.
      destruct (vais_vals_len S C [(i32 c)] ts0 ts4 [T_i32])...

      apply vais_ainstrs_app_nil_l. 
      eapply VAIS_snoc with (ts := []);
        try rewrite app_nil_r...
      (* ⊢a *)
      eapply VAI_label...
      apply vis_to_vais...
Qed.

(* ================================================================= *)
(** ** Preservation - Main Theorem *)

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
  gen C ts1 ts2.
  dependent induction HSC; intros.
  - (* SC_simple *) 
    splits...
    + (*  ⊢S S' ⪯ S' *) apply (extend_store_refl _ HVS).
    + (*  ⊢a*  *) eapply preservation_SC_simple...
  - (* SC_block *)
    splits...
    + (*  ⊢S S' ⪯ S' *) apply (extend_store_refl _ HVS).
    + (*  ⊢a*  *) eapply preservation_SC_block...

  - (* SC_loop *) 
    splits...
    + (*  ⊢S S' ⪯ S' *) apply (extend_store_refl _ HVS).
    + (*  ⊢a*  *) eapply preservation_SC_loop...

  - (* [SC_if__nez] *) 
    splits...
    + (*  ⊢S S' ⪯ S' *) apply (extend_store_refl _ HVS).
    + (*  ⊢a*  *) eapply preservation_SC_if__nez with (c := c) (instrs2 := instrs2)...

  - (* SC_if2 *) 
    splits...
    + (*  ⊢S S' ⪯ S' *) apply (extend_store_refl _ HVS).
    + (*  ⊢a*  *) eapply preservation_SC_if__eqz with (c := I32.zero) (instrs1 := instrs1)... 

  - (* SC_E *) admit.
Admitted.


(* ================================================================= *)
(** ** Preservation - Top Level Frame *)

Lemma VMI_with_ret_none : forall S mi C,
    S ⊢mi mi ∈ C ->
    S ⊢mi mi ∈ C with_return = None.
Proof with eauto.
  introv HVMI.
  inverts HVMI. 
  econstructor...
Qed.

Lemma VA_with_ret_none : forall S F C,
    S ⊢A F ∈ C ->
    S ⊢A F ∈ C with_return = None.
Proof with eauto.
  introv HVA.
  inverts HVA as HVMI HVVS.
  asserts_rewrite ((C0 with_locals = ts with_return = None) = (C0 with_return = None with_locals = ts))...
  eapply VA...
  apply VMI_with_ret_none...
Qed.

Corollary preservation__toplevel : forall S T S' T' rt,
    ⊢c (S, T) ∈ rt ->
    $(S, T) ↪ $(S', T') ->
    ⊢c (S', T') ∈ rt /\ ⊢S S ⪯ S'.
Proof with eauto.
  introv HVC.

  (* valid_config *)
  inverts HVC as HVS HVT. (* valid_store *) (* valid_thread *)
    inverts HVT as HVA HVAIS. (* valid_frame *) (* valid_admin_instrs *)

  introv HSC. simpl in HSC.
  destruct T' as [F' ainstrs'].

  destruct (preservation S F S' F' (C with_return = None) ainstrs ainstrs' [] rt) as (HES & HVS' & HVA' & HVAIS')...
  eapply VA_with_ret_none...
Qed.


(* ================================================================= *)
(** ** Experimenting on [Preservation_SC_E] here *)

Definition prepend_labels (C: context) (xs: list resulttype) :=
  {|
    C_locals := C.(C_locals);
    C_types := C.(C_types);
    C_funcs := C.(C_funcs);
    C_tables := C.(C_tables);
    C_labels := xs ++ C.(C_labels);
    C_return := C.(C_return);
  |}.
Notation "C ',labels*' xs" :=  
  (prepend_labels C xs)
  (at level 67, left associativity) : wasm_scope.

Lemma prepend_labels_ϵ : forall C,
  C = C,labels* [].
Proof with auto.
  introv.
  destruct C.
  unfold prepend_labels; simpl...
Qed.

(* We have need to include the information that
   other field are the same!!
 *)
Reserved Notation "⊢C C1 '⪯' C2 " (at level 70).
Inductive extend_context : context -> context -> Prop :=

  | EC: forall C rts,
      ⊢C C ⪯ (C,labels* rts)

where "⊢C C1 '⪯' C2 "  := (extend_context C1 C2).
Hint Constructors extend_context.


Lemma extend_context_refl: forall C,
    ⊢C C ⪯ C.
Proof with auto.
  introv.
  specialize (EC C []) as HEC. 
  rewrite <- prepend_labels_ϵ in HEC...
Qed.

Lemma extend_context_cons: forall C C' ts,
    ⊢C C,labels ts ⪯ C' ->
    ⊢C C           ⪯ C'.
Proof with eauto.
  introv HEC.
  inverts HEC as HClabel'.
  unfold prepend_labels.
  unfold cons_labels.
  simpl.
  rewrite cons_to_app.
  rewrite app_assoc.
  eapply EC with (rts := rts ++ [ts]).
Qed. 


(*
      S, C  ⊢ E[ainstrs] : ts1 --> ts2
   ------------------------------
      S, C' ⊢   ainstrs  : ts3 --> ts4

      S, C  ⊢ E : labels rts, ts3 --> ts4 |> ts1 --> ts2

      let C' = C, labels (compute_label E) in

   where C' = C, labels... (as deep as the numbers of labels in E)
      we have to include this information as well.
      the numbers of labels in E. 
*)
Lemma plug_E_inner : forall S C E ainstrs ts1 ts2,
   (S, C) ⊢a* (plug__E E ainstrs) ∈ ts1 --> ts2 ->
   exists ts3 ts4 C',   (* E_label -> VAI_label need C with new label *)
    (S, C') ⊢a* ainstrs ∈ ts3 --> ts4 /\ ⊢C C ⪯ C'. 
Proof with eauto.
  introv.
  gen C ainstrs ts1 ts2. (* it's important here to generalize C, i.e. include it in IH *)
  induction E; 
  introv HVAIS; simpl in *.
  - (* E_hole *)
    exists ts1 ts2 C...
    split; try apply extend_context_refl...
  - (* E_seq *)
    apply vais_app3 in HVAIS.
    destruct HVAIS as (ts3 & ts4 & HVAIS0 & HVAIS1 & HVAIS2).
    apply IHE in HVAIS1 as IH.
    destruct IH as (ts3' & ts4' & HVAIS')...
  - (* E_label *)
    inverts HVAIS as HVAIS' HVAI Heq; 
      try (symmetry in Heq; invert_eq_snoc_app Heq).
    inverts HVAI as HVAIS__cont HVAIS__E.
    destruct (IHE _ _ _ _ HVAIS__E) as (ts3' & ts4' & C' & H1 & H2).
    eexists; eexists; eexists.
    split...
    apply extend_context_cons in H2...
Qed.

(*
      S,C  ⊢ E[ainstrs] : ts1 --> ts2
      S,C' ⊢   ainstrs  : ts3 --> ts4  
      S,C' ⊢   ainstrs' : ts3 --> ts4     ⊢ C ⪯ C'
   ----------------------------------------------------
      S,C  ⊢ E[ainstrs']: ts1 --> ts2

  This can only be proved if we include the inforamtion ,
  we might need some thing like:

      ⊢ C ⪯ C' <to> E

*)
Lemma plug_E_same : forall S C C' E ainstrs ainstrs' ts1 ts2 ts3 ts4,
   ⊢C C ⪯ C' ->
   (S, C) ⊢a* (plug__E E ainstrs) ∈ ts1 --> ts2 ->
   (S, C') ⊢a* ainstrs ∈ ts3 --> ts4 ->
   (S, C') ⊢a* ainstrs' ∈ ts3 --> ts4 ->
   (S, C) ⊢a* (plug__E E ainstrs') ∈ ts1 --> ts2.
Proof with eauto.
  introv HEC Hin Hin' Hplug.
  dependent induction E; simpl in *. 
  - (* E_hole *) admit.
  - (* E_seq *) admit.
  - (* E_label *) admit.
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

Theorem preservation_SC_E : forall S F S' F' C ainstrs ainstrs' ts1 ts2,
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
  remember (S, F, ainstrs) as SF.
  remember (S', F', ainstrs') as SF'.
  gen S F ainstrs S' F' ainstrs' C ts1 ts2.
  induction HSC; intros;
    inverts HeqSF; inverts HeqSF'.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - 

(*
        ainstrs  :     ts2 --> ts5
      E[ainstrs] : ts1     -->     ts6
        ainstrs' :     ts2 --> ts3
   -------------------------------------
      E[ainstrs']: ts1     -->     ts4

    ⊢S S ok ->                                (* valid_store  *) 
    S ⊢A F ∈ C ->                             (* valid_frame *)
    (S,C) ⊢a* E[ainstrs0] ∈ ts1 --> ts2 ->    (* valid_admin_instr *)

    (S, F, E[ainstrs0]) ↪ (S', F', E[ainstrs0']) ->  (* HSC *)
    (S, F, ainstrs0) ↪ (S', F', ainstrs'0) ->        (* HSC - sub-structure *)

    (S,C,labels ts...) ⊢a* ainstrs0 ∈ ts3 --> ts4 ->    (* valid_admin_instr *)

    (S,C,labels ts...) ⊢a* ainstrs0' ∈ ts3 --> ts4 ->    (* valid_admin_instr *)

key point: E might be label and cons label, [plug__E] uncons the labels.
 -------------------------------------------------------------------------------

    ⊢S S ⪯ S' /\                             (* weakening *)
      ⊢S S' ok /\                            (* valid_store *)
      S' ⊢A F' ∈ C /\                        (* valid_frame  *)
      (S',C) ⊢a* E[ainstrs'0] ∈ ts1 --> ts2. (* valid_admin_instr *)
*)

    specialize (plug_E_inner _ _ _ _ _ _ HVAIS) as (ts3 & ts4 & C' & Hinner & HEC).
    edestruct IHHSC with (S := S0) (C := C') as (HES & HVS' & HVA' & HVAIS') ...

(* labels have no effect on valid frame and valid moduleinst?? *)
Lemma VMI_weakening_ES : forall S C C' mi,
      ⊢C C ⪯ C' ->
    S ⊢mi mi ∈ C ->
    S ⊢mi mi ∈ C'. (* this is not true since valid_moduleinst ask labels to be ϵ! *)
Proof with eauto.
  introv HEC HVMI.
  inverts HVMI.
  inverts HEC.
  unfold prepend_labels. simpl. rewrite app_nil_r.
Abort.

Lemma VF_weakening_ES : forall S F C C' ,
      ⊢C C ⪯ C' ->
    S ⊢A F ∈ C ->
    S ⊢A F ∈ C'.
Proof with eauto.
Abort.

    admit.
    splits...
    (* only valid_admin_instrs remain, but with different store (up to weakening),
       we need state some a store weakening version of [plug_E_same]
     *)

Abort.



(* ================================================================= *)
(** ** Archive *)

Lemma preservation_SC_simple_old : forall S C ainstrs ainstr__N ainstrs' ts0 ts2 ts3,
      (S,C) ⊢a* ainstrs ∈ [] --> (ts0 ++ ts2)  -> (* [HVAIS] *)
      (S,C) ⊢a  ainstr__N ∈ ts2 --> ts3 ->          (* [HVAI__N] *)
      ainstrs ++ [ainstr__N] ↪s ainstrs' ->        (* [HSS] *)
(* -------------------------------------------------------------- *)
      (S,C) ⊢a* ainstrs' ∈ [] --> (ts0 ++ ts3).
Proof with eauto.
  Admitted. (* save for later testing *)


Theorem preservation_old : forall S T S' T' rt,
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
          eapply preservation_SC_simple_old...

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


