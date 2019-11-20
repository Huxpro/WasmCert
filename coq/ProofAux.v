(* ***************************************************************** *)
(* ProofAux.v                                                        *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)

(* ################################################################# *)
(** * Proof Auxilaries *)

From Wasm Require Export Validation.
From Wasm Require Export Execution.
From Wasm Require Export ExtendedValidation.


(* ================================================================= *)
(** ** Common Definition to state properties *)

Definition relation (X: Type) := X -> X -> Prop.


(* ================================================================= *)
(** ** Snoc *)

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


(* ================================================================= *)
(** ** Snoc App (Snoc-style Append) *)

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
(** *** Snoc app 2 i.e. (xs' ++ [x1; x2]) *)

Lemma snoc_app2_as_snoc_app: forall {X:Type} (ys xs': list X) (x1 x2: X),
    ys = xs' ++ [x1; x2] <->
    ys = (xs' ++ [x1]) ++ [x2].
Proof with auto.
  split; intros H; subst; 
    rewrite <- app_assoc; simpl...
Qed.


(* ================================================================= *)
(** ** Unsnoc, destruct car/cdr by snoc *)

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


(* ================================================================= *)
(** ** Equal Snoc App *)

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

(* By introducing the [Fixpoint unsnoc] we add some computational power
   that [simpl] can perform later. *)
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
Ltac invert_eq_snoc_app_contra Heq cdr car :=
    try solve [
          apply eq_unsnoc_car_eq in Heq;
          simpl in Heq;
          rewrite -> (unsnoc_car_snoc_app_some cdr car) in Heq;
          inverts Heq
        ].

(* A powerful pack of both discharging and computing *)
Ltac invert_eq_snoc_app_pack Heq cdr car :=
  invert_eq_snoc_app_contra Heq cdr car;
  invert_eq_snoc_app_compute Heq.

(* After testing, we found the [invert_eq_snoc_app_compute] ltac can
   also solve the contradictive cases. so we simply do an alias 
 *)
Ltac invert_eq_snoc_app Heq :=
  invert_eq_snoc_app_compute Heq.

Module InvertEqSnocAppTest.

  Lemma nil_case : forall cdr,
      [] = cdr ++ [3] ->
      2 = 3.
  Proof.
    introv Heq.
    dup.
    - invert_eq_snoc_app_contra Heq cdr 3.  (* works! *)
    - invert_eq_snoc_app_compute Heq.  (* also works! *)
  Qed.

  Lemma discharge : forall cdr,
      [1; 2] = cdr ++ [3] ->
      2 = 3.
  Proof.
    introv Heq.
    dup.
    - invert_eq_snoc_app_contra Heq cdr 3.
    - invert_eq_snoc_app_compute Heq. 
  Qed.

  Lemma compute : forall cdr,
      [1; 2] = cdr ++ [2] ->
      2 = 2.
  Proof.
    introv Heq.
    dup.
    - invert_eq_snoc_app_contra Heq cdr 3. (* doesn't work *)
      invert_eq_snoc_app_compute Heq. reflexivity.  (* works *)
    - invert_eq_snoc_app Heq. reflexivity.
  Qed.

End InvertEqSnocAppTest.

(* ----------------------------------------------------------------- *)
(** ** Map Equal Snoc App *)

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


(* ================================================================= *)
(** ** Equality/Injectivitiy on Lifting *)

(* ----------------------------------------------------------------- *)
(** *** Injectivitiy *)

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


(* ----------------------------------------------------------------- *)
(** *** Equality (on app) *)

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

(* ----------------------------------------------------------------- *)
(** *** Equality (on cons) *)

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