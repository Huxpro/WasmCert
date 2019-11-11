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
(** ** List Aux - [snoc] or [snoc-app], a.k.a append-unit-on-tail *)


(* ----------------------------------------------------------------- *)
(** *** Snoc *)

Fixpoint snoc {X: Type} (l: list X) (x: X) : list X :=
  match l with
    | [] => [x]
    | h :: t => h :: (snoc t x)
  end.

Lemma snoc_length: forall {X: Type} (l: list X) (x: X),
  length (snoc l x) = (length l) + 1.
Proof.
  intros X l x.
  induction l as [| x' l' ].
  reflexivity.
  simpl.
  rewrite -> IHl'.
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


(* ----------------------------------------------------------------- *)
(** *** Snoc_app, or Snoc-style Append *)

Lemma snoc_eq_snoc_app: forall {X: Type} (l: list X) (x: X),
    snoc l x = l ++ [x].
Proof.
  intros X l x.
  induction l.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

(* It's named [app_inj_tail] in the standard lib [List.v], but it's a little bit
   misleading in that [tail] usually refers to list, not unit (singleton). e.g.

   Check app_inj_tail.
   Check app_inv_tail.

 *)
Lemma snoc_app_inj: forall {X: Type} (l1 l2: list X) (x1 x2: X),
    l1 ++ [x1] = l2 ++ [x2] <->
    l1 = l2 /\ x1 = x2.
Proof.
  split.
  - apply app_inj_tail.
  - intros [H1 H2]. subst. reflexivity.
Qed.

(* easier to prove via [snoc_app_inj] *)
Lemma snoc_inj: forall {X: Type} (l1 l2: list X) (x1 x2: X),
    snoc l1 x1 = snoc l2 x2 ->
    l1 = l2 /\ x1 = x2.
Proof with auto.
  introv H.
  asserts_rewrite (snoc l1 x1 = l1 ++ [x1]) in H. apply snoc_eq_snoc_app.
  asserts_rewrite (snoc l2 x2 = l2 ++ [x2]) in H. apply snoc_eq_snoc_app.
  apply app_inj_tail...
Qed.


Lemma snoc_app_eq_unit : forall {X: Type} (xs: list X) (x1 x2: X),
    xs ++ [x1] = [x2] ->
    xs = [] /\ x1 = x2.
Proof with auto.
  introv Heq.
  apply app_eq_unit in Heq.
  destruct Heq as [[H1 H2] | [H3 H4]].
  split...
  - inverts H2...
  - inverts H4...
Qed.

Lemma eq_len_eq : forall {X: Type} (xs1 xs2: list X), 
    xs1 = xs2 -> length xs1 = length xs2.
Proof with auto.
  introv Heq.
  subst...
Qed.

Lemma plus_0_n_rev : forall x y,
    x + y = y -> x = 0.
Proof. 
  intros. omega.
Qed.

Lemma snoc_app_eq_same_len : forall {X: Type} (xs xs1 xs2: list X), 
    length xs1 = length xs2 ->
    xs ++ xs1 = xs2 ->
    xs = [] /\ xs1 = xs2.
Proof with auto.
  introv Heqlen Heq.
  assert (Hnil : xs = []).
  { apply eq_len_eq in Heq.
    rewrite app_length in Heq.
    rewrite Heqlen in Heq.
    apply plus_0_n_rev in Heq.
    apply length_zero_iff_nil...
  }
  subst...
Qed.
        


(* ----------------------------------------------------------------- *)
(** *** Unsnoc, destruct car/cdr by snoc *)

Fixpoint unsnoc {X: Type} (l: list X) : option (list X * X) :=
  match l with
    | [] => None 
    | [x] => Some ([], x)
    | x :: xs =>
      match (unsnoc xs) with
        | Some (cdr, car) => Some (x :: cdr, car)
        | None => None
      end
  end.

(* Similar with [last] but returning option *)
Fixpoint unsnoc_car {X: Type} (l: list X) : option X :=
  match l with
    | [] => None
    | [x] => Some x
    | _ :: xs => (unsnoc_car xs)
  end.

(* the similar weakening for [unsnoc] need to consider [cdr] part *)
Lemma unsnoc_car_weaken: forall {X: Type} (xs: list X) (x: X),
    xs <> [] ->
    unsnoc_car (x::xs) = unsnoc_car xs.
Proof.
  intros.
  destruct xs.
  - false H. reflexivity.
  - remember (x0 :: xs) as xs'.
    simpl. subst. reflexivity.
Qed.

Lemma exists_unsnoc: forall {X: Type} (xs : list X), 
    xs <> [] ->
    exists xs' x, unsnoc xs = Some (xs', x). 
Proof with auto.
  introv Hneq.
  induction xs.
  - contradiction Hneq...
  - destruct xs eqn:Hd.
    + exists (@nil X) a...
    + destruct IHxs.
      ++ intros H. inverts H.
      ++ destruct H.
         exists (a::x0) x1.
         remember (x::l) as xs'.
         simpl.
         rewrite Heqxs'.
         rewrite <- Heqxs'.
         rewrite H.
         reflexivity.
Qed.

(* Similar with [exists_last] *)
Lemma exists_unsnoc_car: forall {X: Type} (xs : list X), 
    xs <> [] ->
    exists x, unsnoc_car xs = Some x.
Proof with auto.
  introv Hneq.
  induction xs.
  - contradiction Hneq...
  - destruct xs eqn:Hd.
    + exists a...
    + destruct IHxs.
      ++ intros H. inverts H.
      ++ exists x0.
         remember (x::l) as xs'.
         simpl.
         rewrite Heqxs'.
         rewrite <- Heqxs'.
         rewrite H.
         reflexivity.
Qed.
      
Lemma unsnoc_car_nil : forall {A : Type} (l : list A), 
    unsnoc_car l = None ->
    l = nil.
Proof. 
  introv H.
  destruct l.
  - reflexivity.
  - assert (Ha : a :: l <> []).
    + unfold not. intro Hn. inverts Hn.
    + apply exists_unsnoc_car in Ha. destruct Ha. 
      rewrite H in H0. inverts H0.
Qed.

Lemma eq_unsnoc_eq: forall {A : Type} (l1 l2 : list A), 
  l1 = l2 ->
  unsnoc l1 = unsnoc l2.
Proof with auto. 
  introv Heq.
  gen l2. induction l1; destruct l2; intros.
  - reflexivity.
  - inverts Heq.
  - inverts Heq.
  - injection Heq. intros; subst...
Qed.

Lemma eq_unsnoc_car_eq: forall {A : Type} (l1 l2 : list A), 
  l1 = l2 ->
  unsnoc_car l1 = unsnoc_car l2.
Proof with auto. 
  introv Heq.
  gen l2. induction l1; destruct l2; intros.
  - reflexivity.
  - inverts Heq.
  - inverts Heq.
  - injection Heq. intros; subst...
Qed.

Lemma unsnoc_neq: forall {A : Type} (l1 l2 : list A), 
  unsnoc l1 <> unsnoc l2 ->
  l1 <> l2.
Proof. 
  Admitted.

Lemma unsnoc_car_neq: forall {A : Type} (l1 l2 : list A), 
  unsnoc_car l1 <> unsnoc_car l2 ->
  l1 <> l2.
Proof. 
  Admitted.

Lemma unsnoc_snoc_app_some : forall {X: Type} (l: list X) x,
    unsnoc (l ++ [x]) = Some (l, x).
Proof. 
  Admitted.

Lemma unsnoc_some_eq_snoc_app: forall {X: Type} {xs xs' : list X} {x: X},
  unsnoc xs = Some (xs', x) ->
  xs = xs' ++ [x].
Proof with auto.
  destruct xs;
    introv Heq.
  - simpl in Heq. inverts Heq.
  - gen x xs'. induction xs; intros.
    + simpl in Heq. inverts Heq. apply app_nil_l.
    + admit.
Admitted.

(* combine *)
Lemma exists_snoc_app: forall {X: Type} (xs : list X), 
    xs <> [] ->
    exists xs' x, xs = xs' ++ [x].
Proof with auto.
  introv H.
  apply exists_unsnoc in H.
  destruct H as (xs' & x & Heq).
  exists xs' x.
  apply unsnoc_some_eq_snoc_app...
Qed.

Lemma cons_to_snoc_app: forall {X: Type} (x : X) (xs : list X), 
    exists xs' x', (x::xs) = xs' ++ [x'].
Proof with eauto.
  intros.
  destruct (exists_snoc_app (x::xs)) as (xs' & x' & Heq).
  unfold not; intros Hcontra; symmetry in Hcontra; eapply nil_cons...
  exists xs' x'...
Qed.

Lemma unsnoc_car_snoc_app_some : forall {X: Type} (l: list X) x,
    unsnoc_car (l ++ [x]) = Some x.
Proof. 
  Admitted.

Lemma unsnoc_snoc_some : forall {X: Type} (l: list X) x,
    unsnoc (snoc l x) = Some (l, x).
Proof. 
  Admitted.

Lemma unsnoc_car_snoc_some : forall {X: Type} (l: list X) x,
    unsnoc_car (snoc l x) = Some x.
Proof. 
  Admitted.

(* This give only the existentials but could not take advantages of Coq computing engine. *) 
Lemma eq_snoc_app_split_exist: forall {X:Type} (ys xs': list X) (x: X),
    ys = xs' ++ [x] ->
    exists ys' y,
      ys = ys' ++ [y] /\ ys' = xs' /\ y = x.
Proof with auto.
  introv Heq.
  destruct ys as [ | y ys'] eqn:Heqys.
  - (* [] - prove it's impossible *)
    symmetry in Heq. apply app_eq_nil in Heq.
    destruct Heq as [H1 Hconstr]. inverts Hconstr.
  - (* :: then we can construct the existential *)
    assert (Hneq : ys <> []). { subst. unfold not; intros. inverts H. }
    destruct (exists_unsnoc ys Hneq) as (cdr & car & Hunsnoc).
    exists cdr car.
    split.
    + subst ys. rewrite -> Heq in *.
      rewrite unsnoc_snoc_app_some in Hunsnoc.
      inverts keep Hunsnoc. reflexivity.
    + (* prove cdr ++ [car] = xs' ++ [x] *)
      rewrite <- Heqys in Heq.
      apply eq_unsnoc_eq in Heq. 
      rewrite -> Hunsnoc in Heq.
      rewrite unsnoc_snoc_app_some in Heq.
      splits; injection Heq; auto.
Qed.

(* By introducing the [Fixpoint unsnoc] we add some computing power for [simpl] to perform. *)
Lemma eq_snoc_app_split_unsnoc: forall {X:Type} (ys xs': list X) (x: X),
    ys = xs' ++ [x] ->
    unsnoc ys = Some (xs', x).
Proof with auto.
  introv Heq.
  apply eq_snoc_app_split_exist in Heq.
  destruct Heq as (ys' & y & Heq & Hys' & Hy).
  rewrite -> Heq.
  asserts_rewrite (unsnoc (ys' ++ [y]) = Some (ys', y)).
  apply unsnoc_snoc_app_some.
  subst...
Qed.

(* Invert when the snoc-append equation does hold,
   This will perform the Coq computation and subst the generated equality.
 *)
Ltac invert_eq_snoc_app_compute Heq :=
  apply eq_snoc_app_split_unsnoc in Heq;
  inverts Heq.


(* Inverts when the snoc-append equation does not hold
   This is for discharging cases that are invalid.
 *)
Ltac invert_eq_snoc_app_discharge Heq cdr car :=
    try solve [
          apply eq_unsnoc_car_eq in Heq;
          simpl in Heq;
          rewrite -> (unsnoc_car_snoc_app_some cdr car) in Heq;
          inverts Heq
        ].

(* A powerful pack of both discharging and computing *)
Ltac invert_eq_snoc_app Heq cdr car :=
  invert_eq_snoc_app_discharge Heq cdr car;
  invert_eq_snoc_app_compute Heq.


Module InvertEqSnocAppTest.

  Lemma nil_case : forall cdr,
      [] = cdr ++ [3] ->
      2 = 3.
  Proof.
    introv Heq.
    dup.
    - invert_eq_snoc_app_discharge Heq cdr 3.  (* works! *)
    - invert_eq_snoc_app_compute Heq.  (* also works! *)
  Qed.

  Lemma discharge : forall cdr,
      [1; 2] = cdr ++ [3] ->
      2 = 3.
  Proof.
    introv Heq.
    dup.
    - invert_eq_snoc_app_discharge Heq cdr 3.
    - invert_eq_snoc_app_compute Heq. 
  Qed.

  Lemma compute : forall cdr,
      [1; 2] = cdr ++ [2] ->
      2 = 2.
  Proof.
    introv Heq.
    dup.
    - invert_eq_snoc_app_discharge Heq cdr 3. (* doesn't work *)
      invert_eq_snoc_app_compute Heq. reflexivity.  (* works *)
    - invert_eq_snoc_app Heq cdr 3. reflexivity.
  Qed.

End InvertEqSnocAppTest.


(* This map version gave what we want. *)
Lemma map_eq_snoc_app_split: forall {X:Type} {Y: Type} (ys : list Y) (xs': list X) (x: X) (f: Y -> X),
    map f ys = xs' ++ [x] ->
    exists ys' y,
      ys = ys' ++ [y] /\ map f ys' = xs' /\ f y = x.
Proof with auto.
  introv Heq.
  destruct ys as [ | y ys'] eqn:Heqys.
  - (* ys = [] - prove it's impossible *)
    symmetry in Heq.
    apply app_eq_nil in Heq.
    destruct Heq as [H1 Hconstr]. inverts Hconstr.
  - (* ys <> [] - then we can unsnoc it and instantiate the existentials *)
    assert (Hneq : ys <> []) by (apply not_eq_sym; subst; apply nil_cons).  
    destruct (exists_unsnoc ys Hneq) as (cdr & car & Hunsnoc).
    apply unsnoc_some_eq_snoc_app in Hunsnoc.
    rewrite <- Heqys in Heq.
    rewrite -> Hunsnoc in Heq.
    rewrite map_app in Heq.
    simpl in Heq.
    apply snoc_app_inj in Heq.

    exists cdr car.
    split; try subst; assumption. 
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
(** ** Lemma - equality/injectivitiy between lifting *)

(* constructors are injective
   so we don't need to prove Plain and Const is injective... 

   but we need to prove [map] preserve injectivity.
 *)

Lemma map_inj_inj: forall {X Y: Type} (f: X -> Y) (xs1 xs2: list X),
    (forall x1 x2, f x1 = f x2 -> x1 = x2) ->
    map f xs1 = map f xs2 ->
    xs1 = xs2.
Proof with auto.
  introv Hinj Heq.
  gen xs2. induction xs1; intros.
  - simpl in Heq. symmetry in Heq. apply map_eq_nil in Heq. subst...
  - destruct xs2.
    + inverts Heq.
    + asserts_rewrite (map f (a :: xs1) = f a :: map f xs1) in Heq. apply map_cons.
      asserts_rewrite (map f (x :: xs2) = f x :: map f xs2) in Heq. apply map_cons.
      inverts Heq.
      apply Hinj in H0.
      apply IHxs1 in H1.
      subst...
Qed.

Lemma up_inj : forall instrs1 instrs2,
    ↑instrs1 = ↑instrs2 ->
     instrs1 =  instrs2.
Proof with eauto.
  intros.
  apply (map_inj_inj Plain)...
  introv Hinj; inverts Hinj...
Qed.
    

Lemma lift_vals_inj : forall vals1 vals2,
    lift_vals vals1 = lift_vals vals2 ->
              vals1 =           vals2.
Proof with auto.
  intros.
  apply (map_inj_inj Const)...
  introv Hinj. inverts Hinj...
Qed.

Lemma upup_inj : forall vals1 vals2,
    ⇈vals1 = ⇈vals2 ->
     vals1 =  vals2.
Proof with auto.
  intros.
  remember (map Const vals1) as instrs1.
  remember (map Const vals2) as instrs2.
  apply up_inj in H.
  apply lift_vals_inj; subst...
Qed.


Lemma up_app : forall instrs1 instrs2,
  ↑(instrs1 ++ instrs2) = ↑instrs1 ++ ↑instrs2.
Proof.
  apply map_app.
Qed.

Lemma lift_vals_app : forall vals1 vals2,
  lift_vals (vals1 ++ vals2) = lift_vals vals1 ++ lift_vals vals2.
Proof.
  apply map_app.
Qed.

Lemma upup_app : forall vals1 vals2,
  ⇈(vals1 ++ vals2) = ⇈vals1 ++ ⇈vals2.
Proof.
  intros.
  remember (map Const vals1) as instrs1.
  remember (map Const vals2) as instrs2.
  remember (map Const (app vals1 vals2)) as instrs_app.
  asserts_rewrite (instrs_app = instrs1 ++ instrs2).
  - subst. apply lift_vals_app.
  - apply up_app.
Qed.

Lemma upup_cons : forall val vals,
  ⇈(val :: vals) = Plain (Const val) :: ⇈vals.
Proof.
  intros.
  remember (Const val) as head.
  remember (map Const vals) as tail.
  remember (map Const (cons val vals)) as list.
  asserts_rewrite (list = head :: tail).
  - subst. apply map_cons.
  - apply map_cons.
Qed.


Lemma unsnoc_car_vals : forall vals,
    unsnoc_car (⇈vals) = None \/ exists val, unsnoc_car (⇈vals) = (Some (Plain (Const val))).
Proof with auto.
  intros. 
  induction vals.
  - left. simpl...
  - right.
    assert (H: ⇈(a :: vals) <> []).
    + unfold not. intros. inverts H.
    + destruct IHvals.
      ++ (* None *)
        apply unsnoc_car_nil in H0.
        apply map_eq_nil in H0.
        apply map_eq_nil in H0.
        subst. 
        exists a. simpl...
      ++ (* Some *)
        destruct vals.
        +++ (* [a] *) exists a...
        +++ (* a :: v :: vals *)
          assert (Ha: unsnoc_car (⇈ (a :: v :: vals)) = unsnoc_car (⇈ (v :: vals))).
          ++++ apply unsnoc_car_weaken. unfold not; intros Hn; inversion Hn.
          ++++ destruct H0. exists x. subst...
Qed.
      

(* ================================================================= *)
(** ** Lemma - Normal Form *)

Definition relation (X: Type) := X -> X -> Prop.

Definition normal_form {X : Type} (R : relation X) (x : X) : Prop :=
  ~ exists x', R x x'.

Lemma vals_normal_form_step_simple : forall vals,
    normal_form step_simple (⇈vals).
Proof.
  unfold normal_form. introv. intros H.
  inverts H as. intros ainstrs' HSC.
  inverts HSC;
   try (inverts H;
        apply eq_unsnoc_car_eq in H2;
        simpl in H2;
        specialize (unsnoc_car_vals vals);
        intros [ Hnone | Hsome ];
        try (rewrite -> Hnone in H2; inverts H2);
        try (destruct Hsome; rewrite -> H in H2; inverts H2)).
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

(* snoc a [val] should be either ill-formed or, normally, all [val] *)
Lemma ainstrs_snoc_app_val_normal_form_step_simple: forall ainstrs val, 
    normal_form step_simple (ainstrs ++ ⇈[val]).
Proof.
  unfold normal_form. introv. intros H.
  inverts H as. intros ainstrs' HSC.
  inverts HSC;
    try(apply eq_unsnoc_car_eq in H;
        simpl in H;
        specialize (unsnoc_car_snoc_app_some ainstrs (Plain (Const val)));
        intros Hsome;
        rewrite -> Hsome in H;
        inverts H).
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

  - (* [SC_trap__E] *)
    intros HE.
    apply plug_E_ϵ in HE; subst.
    inverts HE.
Qed.


(* ================================================================= *)
(** ** Lemma - Unproved/Unused *)




(* ================================================================= *)
(** ** Preservation - VAIS_snoc -> SC_simple*)


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
    inverts HVI__N.

    + (* VI_const *)
      exfalso.
      simpl in HSS.
      apply (ainstrs_snoc_app_val_normal_form_step_simple ainstrs val).
      exists ainstrs'...

    + (* VI_unop *)
      inverts keep HSS as Heval Heq; 
        invert_eq_snoc_app Heq ainstrs (Plain (Unop op)).

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
        invert_eq_snoc_app Heq ainstrs (Plain (Binop op)).

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
        invert_eq_snoc_app Heq ainstrs (Plain (Testop op)).

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
        invert_eq_snoc_app Heq ainstrs (Plain (Relop op)).

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

  - (* VAI_trap *)
    (* Trap can't take a simple step, so all discharged *)
    inverts keep HSS as Heval Heq; 
    invert_eq_snoc_app Heq ainstrs (Trap).

Qed.


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
    admit. (* need to show typing is deterministic *)
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
   (S', C') ⊢a*          ainstrs'  ∈ ts3 --> ts4 ->
   (S', C') ⊢a* (plug__E E ainstrs') ∈ ts1 --> ts6.
Proof with eauto.
  induction E; introv H34 H16 H34'.
  - admit.
  - simpl in *.
    apply vais_app3 in H16 as Happ3.
    destruct Happ3 as (ts2 & ts5 & H12 & H25 & H56). 
    specialize (IHE ainstrs0 ainstrs' ts2 ts3 ts4 ts5 H34 H25 H34') as H25'...
    apply vais_app3.
    exists ts2 ts5. 
    splits.
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
    admit. (* need to show typing is deterministic *)
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


(* generailized preservation *)

Theorem preservation : forall S F S' F' C ainstrs ainstrs' ts1 ts2,
    S ⊢A F ∈ C ->
    (S,C) ⊢a* ainstrs ∈ ts1 --> ts2 ->
    (S, F, ainstrs) ↪ (S', F', ainstrs') ->
    exists C', S' ⊢A F' ∈ C'  /\ (S', C') ⊢a* ainstrs' ∈ ts1 --> ts2.
Proof with eauto.
  introv HVA HVAIS HSC.
  gen ts1 ts2.
  dependent induction HSC; intros.
  - admit.
  - (* SC_E *)
    apply plug_E_inner in HVAIS as Hinner.
    destruct Hinner as (ts3 & ts4 & Hinner).
    edestruct (IHHSC S F S' F' ainstrs0 ainstrs'0) as (C' & HVA' & Hinner')...
    exists C'. split... sort.
Abort.



(* only top level frame *)
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

  dup.
  induction HSC.
  + (* SC_simple *)
    admit.
  + (* SC_E *)
    apply IHHSC.
  + (* SC_E__trap *)
    admit.

  + dependent induction HSC.

  - (* SC_simple *)
    admit.

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

  
   

