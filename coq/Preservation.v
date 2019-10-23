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

From Wasm.Lib Require Export LibTactics.


(* Coercions are too confusing during proofs. *)
Set Printing Coercions.


(**************************************************************)
(** ** Implicit Types - Copied from ExtendedTyping *)

(* Primary *)
Implicit Type b : bool.
Implicit Type n m : nat.

(* Value *)
Implicit Type val : val.
Implicit Type vals : list val.

(* Structure *)
Implicit Type M: module.
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
(** ** List snoc / app - Aux *)

Fixpoint snoc {X: Type} (l: list X) (x: X) : list X :=
  match l with
    | [] => [x]
    | h :: t => h :: (snoc t x)
  end.

Lemma length_snoc: forall {X: Type} (l: list X) (x: X),
  length (snoc l x) = (length l) + 1.
Proof.
  intros X l x.
  induction l as [| x' l' ].
  reflexivity.
  simpl.
  rewrite -> IHl'.
  reflexivity.
Qed.

Lemma snoc_eq_app: forall {X: Type} (l: list X) (x: X),
    snoc l x = l ++ [x].
Proof.
  intros X l x.
  induction l.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

Lemma snoc_app: forall {X: Type} (l1 l2: list X) (x: X),
    snoc (l1 ++ l2) x = l1 ++ snoc l2 x.
Proof.
  intros X l1 l2 x.
  induction l1.
  reflexivity.
  simpl.
  rewrite IHl1.
  reflexivity.
Qed.

Lemma snoc_destruct: forall {X: Type} (l1 l2: list X) (x1 x2: X),
    snoc l1 x1 = snoc l2 x2 ->
    l1 = l2 /\ x1 = x2.
Proof.
  Admitted.

Lemma app_snoc_destruct: forall {X: Type} (l1 l2: list X) (x1 x2: X),
    l1 ++ [x1] = l2 ++ [x2] ->
    l1 = l2 /\ x1 = x2.
Proof.
  Admitted.

Fixpoint unsnoc {X: Type} (l: list X) : option X :=
  match l with
    | [] => None 
    | [x] => Some x
    | _ :: xs => (unsnoc xs)
  end.

Lemma unsnoc_neq: forall {A : Type} (l1 l2 : list A), 
  unsnoc l1 <> unsnoc l2 ->
  l1 <> l2.
Proof. 
  Admitted.

Lemma unsnoc_snoc_app : forall {X: Type} (l: list X) x,
    unsnoc (l ++ [x]) = Some x.
Proof. 
  Admitted.

Lemma unsnoc_snoc : forall {X: Type} (l: list X) x,
    unsnoc (snoc l x) = Some x.
Proof. 
  Admitted.


(* ================================================================= *)
(** ** Lemma - lifting *)

Lemma lift_up_eq : forall instrs1 instrs2,
    ↑instrs1 = ↑instrs2 ->
     instrs1 =  instrs2.
Proof.
  Admitted.

Lemma lift_upup_eq : forall vals1 vals2,
    ⇈vals1 = ⇈vals1 ->
     vals1 =  vals2.
Proof.
  Admitted.

Lemma lift_vals_eq : forall vals1 vals2,
    lift_vals vals1 = lift_vals vals1 ->
    vals1 =  vals2.
Proof.
  Admitted.

(* using [Lemma map_app] *)

Lemma lift_up_app : forall instrs1 instrs2,
  ↑(instrs1 ++ instrs2) = ↑instrs1 ++ ↑instrs2.
Proof.
  Admitted.

Lemma lift_upup_app : forall vals1 vals2,
  ⇈(vals1 ++ vals2) = ⇈vals1 ++ ⇈vals2.
Proof.
  Admitted.

Lemma lift_vals_app : forall vals1 vals2,
  lift_vals (vals1 ++ vals2) = lift_vals vals1 ++ lift_vals vals2.
Proof.
  Admitted.


(* ================================================================= *)
(** ** Lemma - Aux *)

Lemma plug_E_ϵ : forall E ainstrs, 
  plug__E E ainstrs = [] ->
  ainstrs = [].
Proof.
  Admitted.

(* if the snoc is [val], then all [val] *)
Lemma snoc_val_is_normal_form2: forall ainstrs val, 
  ~ exists ainstrs', ainstrs ++ ⇈[val] ↪s ainstrs'.
Proof.
  Admitted.
      
Lemma snoc_val_is_normal_form: forall instrs val, 
  ~ exists ainstrs', ↑(instrs ++ [Const val]) ↪s ainstrs'.
Proof.
  Admitted.


Lemma S_F_ϵ_is_normal_form : forall S F S' F',
  ~ exists ainstrs', (S, F, []) ↪ (S', F', ainstrs').
Proof with auto.
  introv. intros H.
  inverts H as. intros ainstrs' HSC.

  (* want both inversion and induction? [remember] *)
  remember (S, F, []) as S_F_ϵ.     

  induction HSC;
    inverts HeqS_F_ϵ as.

  - (* SC_simple *)
    inversion H.

  - (* SC_E *)
    intros HE.
    apply plug_E_ϵ in HE; subst.
    apply IHHSC...
Qed.

(* We observed this is too strong and we need
   a specific [C] and [ts1] (via [remember].
   also to have a specifc [ts1],
   we need to connect the the resulttype with thread result.
   and discover this spec bug.

    Lemma decompose : forall C instrs instr__N ts0 ts1 ts ts3,
        C ⊢* instrs ∈ ts1 --> (ts0 ++ ts) (* ts2 *) ->
        C ⊢  instr__N ∈ ts --> ts3 ->
        ∃ instrs' vals, instrs ++ [instr__N] = instrs' ++ vals
 *)
     
Lemma decompose : forall C instrs ts0 ts,
    C ⊢* instrs ∈ [] --> (ts0 ++ ts) ->
    exists vals0 vals,
      map type_of vals0 = ts0 -> (* I probably don't care *)
      map type_of vals  = ts ->  (* I care *)
      instrs = map Const (vals0 ++ vals).
Proof.
  Admitted.

Lemma all_of_type : forall C instrs ts,
    C ⊢* instrs ∈ [] --> ts ->
    exists vals,
      map type_of vals = ts -> 
      instrs = map Const vals.
Proof.
  Admitted.


(* ... *)
Lemma functype_inv : forall C instr__N ts0 ts1 ts2,
  C ⊢ instr__N ∈ ts1 --> ts2 ->
  C ⊢ instr__N ∈ (ts0 ++ ts1) --> (ts0 ++ ts2).
Proof.
  Admitted.


Lemma drop_singleton_typing: forall C instr__N ts1 ts2,
    C ⊢* [instr__N] ∈ ts1 --> ts2 ->
    C ⊢ instr__N ∈ ts1 --> ts2.
Proof.
  introv HVIS.
  inverts HVIS.
  replace ([instr__N]) with ([] ++ [instr__N]) in H.
  apply app_snoc_destruct in H.
  inverts H.
  inverts H3. apply functype_inv. assumption.
  apply app_eq_nil in H.
  inverts H.
  false H1.
  reflexivity.
Qed.
  
(* TODO: prov in Numerics.v
   for binop, testop, relop as well.
 *)
Lemma eval_unop_inv : forall op val1 val,
    eval_unop op val1 = Ok (Some val) ->
    type_of op = type_of val.
Proof.
  Admitted.


(* ================================================================= *)
(** ** Lemmas - Cases *)



(* ================================================================= *)
(** ** Main Theorem *)

Theorem preservation : forall S T S' T' rt,
    ⊢c (S, T) ∈ rt ->
    $(S, T) ↪ $(S', T') ->
    ⊢c (S', T') ∈ rt /\ ⊢S S ⪯ S'.
Proof with eauto.
  introv HVC.
  gen S' T'.
  (* valid_config *) inverts HVC as HSok HVT.
  (* valid_thread *) inverts HVT as HVA HVAIS. 
     (* valid_frame *) inverts keep HVA as HVMI HVV.  
     (* valid_admin_instrs *) inverts HVAIS as HVIS.    

  (* Induction on typing derivation of valid_instrs have 2 cases.
     We need to remember all specifics otherwise they will get lost.
   *)
  remember (C0 with_locals = ts with_return = None) as C.
  remember ([] --> rt) as progtype.
  induction HVIS as [ | ? ? ? ? ? ? ? HVIS' IHHVIS' HVI__N ]; (* [eqn:H] failed? *)
    introv HSC;
    simpl in HSC;
    remember {| A_locals := vals; A_module := mi |} as F;
    destruct T' as [F' ainstrs'].

  - (* VIS_empty *)
    exfalso.
    apply (S_F_ϵ_is_normal_form S F S' F'). 
    exists ainstrs'...

  - (* VIS_snoc *)
    remember (S, F, ↑ (instrs ++ [instr__N])) as SF.
    remember (S', F', ainstrs') as SF'.
    induction HSC as [ ? ? ? ? HSS | ];
      inverts Heqprogtype;
      inverts HeqSF;
      inverts HeqSF'.
      
    + (* SC_simple *)
      inverts keep HVI__N. (* invert typing [instrN] *)

      ++ (* VI_const *)
         exfalso.
         simpl in HSS.
         apply (snoc_val_is_normal_form instrs val).
         exists ainstrs'...

      ++ (* VI_unop *)
         inverts HSS as. (* invert [step_simple] relation *)

        +++ (* [SS_unop__some] *)
            introv Heval_unop Heq.

            replace ([Plain (Const val1); Plain (Unop op0)])
               with (↑([Const val1] ++ [Unop op0])) in Heq.
            apply lift_up_eq in Heq.
            apply app_snoc_destruct in Heq.
            inverts Heq as Heqop; inverts Heqop.

            split.
            ++++ constructor.
                 assumption.
                 subst. (* rewrite <- TEMP. *)
                 econstructor. apply HVA.
                 constructor. replace ([Const val]) with ([] ++ [Const val]).
                 eapply VIS_snoc.
                 apply drop_singleton_typing in HVIS'.
                 inverts HVIS'.
                 skip. (* eapply VIS_empty. *)
                 apply VI_const.
                 apply (eval_unop_inv _ val1)...
                 reflexivity.
                 trivial.
            ++++ skip.
            ++++ simpl. reflexivity.

        +++ (* [SS_unop__none] *)
            skip.
           
        +++ (* contradiction *)
            intros.
            replace ([Plain (Const c1); Plain (Const c2); Plain (Binop op0)])
               with (↑([Const c1; Const c2] ++ [Binop op0])) in H.
            apply lift_up_eq in H.
            false H.
            apply unsnoc_neq in H...
            replace (unsnoc ([Const c1; Const c2] ++ [Binop op0])) with (Some (Binop op0)). 
            replace (unsnoc (instrs ++ [Unop op])) with (Some (Unop op)). 
            unfold not; intros. false H1.
            skip. (* eapply (unsnoc_snoc_app instrs (Unop op)).  *)
            skip.  (* eapply unsnoc_snoc_app. *)
            reflexivity.

        +++ (* contradiction *) skip.
        +++ (* contradiction *) skip.
        +++ (* contradiction *) skip.

      (* should be similar with VI_unop,
         will polish the proof and extract them as lemma. *)
      ++ (* VI_binop *)
         admit.
      ++ (* VI_testop *)
         admit.
      ++ (* VI_relop *)
         admit.
                                        
    + (* SC_E *)
      admit.
  
