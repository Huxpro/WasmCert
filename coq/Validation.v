(* ***************************************************************** *)
(* Validation.v                                                      *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)


(* ################################################################# *)
(** * Validation *)

From Wasm Require Export Structure.
From Coq Require Export Structures.Equalities.

(* Test imports/exports *)

Module ImportExportTests.

  Definition ex_fun_nu : functype := [] --> [T_i32].

End ImportExportTests.


(* ================================================================= *)
(** ** Conventions *)
(** http://webassembly.github.io/spec/core/valid/conventions.html *)

(* ----------------------------------------------------------------- *)
(** *** Contexts *)
(** http://webassembly.github.io/spec/core/valid/conventions.html#contexts *)

Record context :=
  {
    C_types : list functype;
    C_funcs : list functype;
    C_tables : list tabletype;
    (* C_mems : list memtype; *)
    (* C_globals : list globaltype; *)
    C_locals : list valtype;
    C_labels : list resulttype;
    C_return : option resulttype;  
  }.

Definition empty_context :=
  {|
    C_types := [];
    C_funcs := [];
    C_tables := [];
    (* C_mems := []; *)
    (* C_globals := []; *)
    C_locals := [];
    C_labels := [];
    C_return := Some [];
  |}.


(** functional update - replacing fields *)

Definition replace_locals(C: context) (xs: list valtype) :=
  {|
    C_locals := xs;
    C_types  := C.(C_types);
    C_funcs  := C.(C_funcs);
    C_tables := C.(C_tables);
    C_labels := C.(C_labels);
    C_return := C.(C_return);
  |}.
Notation "C 'with_locals' = xs" :=
  (replace_locals C xs)
  (at level 68, left associativity) : wasm_scope.

Definition replace_labels (C: context) (xs: list resulttype) :=
  {|
    C_labels := xs;
    C_types := C.(C_types);
    C_funcs := C.(C_funcs);
    C_tables := C.(C_tables);
    C_locals := C.(C_locals);
    C_return := C.(C_return);
  |}.
Notation "C 'with_labels' = x" :=
  (replace_labels C x)
  (at level 68, left associativity) : wasm_scope.

Definition replace_return (C: context) (x: option resulttype) :=
  {|
    C_return:= x;
    C_types := C.(C_types);
    C_funcs := C.(C_funcs);
    C_tables := C.(C_tables);
    C_locals := C.(C_locals);
    C_labels := C.(C_labels);
  |}.
Notation "C 'with_return' = x" :=
  (replace_return C x)
  (at level 68, left associativity) : wasm_scope.


(** functional update - cons on fields *)

Definition cons_labels (C: context) (x: resulttype) :=
  {|
    C_labels := x :: C.(C_labels);
    C_types := C.(C_types);
    C_funcs := C.(C_funcs);
    C_tables := C.(C_tables);
    C_locals := C.(C_locals);
    C_return := C.(C_return);
  |}.
Notation "C ',labels' x" :=
  (cons_labels C x)
  (at level 67, left associativity) : wasm_scope.

Definition cons_locals (C: context) (x: valtype) :=
  {|
    C_locals := x :: C.(C_locals);
    C_types := C.(C_types);
    C_funcs := C.(C_funcs);
    C_tables := C.(C_tables);
    C_labels := C.(C_labels);
    C_return := C.(C_return);
  |}.
Notation "C ',locals' x" :=
  (cons_locals C x)
  (at level 67, left associativity) : wasm_scope.


(** functional update - prepend on fields *)

Definition prepend_locals (C: context) (xs: list valtype) :=
  {|
    C_locals := xs ++ C.(C_locals);
    C_types := C.(C_types);
    C_funcs := C.(C_funcs);
    C_tables := C.(C_tables);
    C_labels := C.(C_labels);
    C_return := C.(C_return);
  |}.
Notation "C ',locals*' xs" :=  
  (prepend_locals C xs)
  (at level 67, left associativity) : wasm_scope.


(** Tests *)

Module ContextTests.

  (* nth is total and require default *)
  Example ex1 : (nth 1 [1;2;3] 0) = 2. auto. Qed.
  Example ex2 : (idx [1;2;3] 1) = Some 2. auto. Qed.

  Example ex_C :=
    {|
      C_types := [];
      C_funcs := [];
      C_tables := [];
      C_locals := [T_i32; T_i32];
      C_labels := [];
      C_return := None;
    |}.

  Example ex3 : (idx ex_C.(C_locals) 0) = Some T_i32. auto. Qed.
  Example ex4 : (idx ex_C.(C_locals) 1) = Some T_i32. auto. Qed.
  Example ex5 : (idx ex_C.(C_locals) 2) = None. auto. Qed.

  (* Testing Updates Notation *)
  Example ex_Crl := ex_C with_labels = [[T_i32]].
  (* Compute ex_Crl. *)

  Example ex_Crr := ex_C with_return = Some [T_i32].
  (* Compute ex_Crr. *)

  Example ex_Crlr := ex_C with_locals = [T_i32] with_return = Some [T_i32].
  (* Compute ex_Crlr. *)

  (* Testing if break pair *)
  Example pair1 := (1,2).
  Example pair2 := (1, 2).

  (* Testing Field Cons Notation *)
  Example ex_Cc0 := ex_C,locals* [T_i32]. 
  (* Compute ex_Cc0. *)

  Example ex_Cc1 := ex_C,labels [T_i32]. 
  (* Compute ex_Cc1. *)

  Example ex_Cc2 := ex_C,labels [T_f32],labels [T_i32]. 
  (* Compute ex_Cc2. *)

  (* Testing associativity *)
  Example ex_Ca1 := ex_C ,labels [T_f32] ,labels [T_i32] with_return = Some [T_i32].
  (* Compute ex_Ca1. *)

  (* Testing Indexing Notation *)
  Example i1 : ([1;2;3].[1] ) = Some 2. auto. Qed.

  Example i2 : (ex_C.(C_locals).[0]) = Some T_i32. auto. Qed.
  Example i3 : (ex_C.(C_locals).[1]) = Some T_i32. auto. Qed.
  Example i4 : (ex_C.(C_locals).[2]) = None. auto. Qed.

  Example i5 : forallb (fun ty => eqb_valtype ty T_i32) ex_C.(C_locals) = true.
  auto. Qed.

  Example i6 : all_valtype ex_C.(C_locals) T_i32 = true.
  auto. Qed.

  Example all_i32 := Forall (fun ty => ty = T_i32) (C_locals ex_C).

  Lemma ex_forall : all_i32.
  Proof with eauto.
    unfold all_i32.
    simpl.
    eapply Forall_cons...
  Qed.

End ContextTests.


(**************************************************************)
(** ** Implicit Types - subset of ExtendedTyping *)

(* Primary *)
Implicit Type b : bool.

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



(* ================================================================= *)
(** ** Types *)
(** http://webassembly.github.io/spec/core/valid/types.html *)

(* ----------------------------------------------------------------- *)
(** *** Limits *)

Reserved Notation "'⊢l' l '∈' k" (at level 70).
Inductive valid_limit : limits -> I32.t -> Prop :=

  (* No max limits *)
  (* should it be [I32. <=] or Coq [<=] ? *)

  | VL__none: forall n k,
      I32.le_u n k = true ->
      ⊢l {| L_min := n; L_max := None |} ∈ k 

  (* Has max limits *)
       
  | VL__some: forall n m k,
      I32.le_u n k = true ->
      I32.le_u m k = true ->
      I32.le_u n m = true ->
      ⊢l {| L_min := n; L_max := (Some m) |} ∈ k

where "'⊢l' l '∈' k " := (valid_limit l k).

Hint Constructors valid_limit.


(* ----------------------------------------------------------------- *)
(** *** Block Types *)
(** https://webassembly.github.io/multi-value/core/valid/types.html#block-types *)

(** Block types may be expressed in one of two forms, both of which are converted to plain function types by the following rules. *)

Reserved Notation "C '⊢bt' bt '∈' ft" (at level 70).
Inductive valid_blocktype : context -> blocktype -> functype -> Prop :=

  | VBT_typeidx: forall C i ft,
      C.(C_types).[i] = Some ft ->
      C ⊢bt BT_typeidx i ∈ ft

  | VBT_valtype__some: forall C t,
      C ⊢bt BT_valtype (Some t) ∈ [] --> [t]

  | VBT_valtype__none: forall C, 
      C ⊢bt BT_valtype None ∈ [] --> []

where "C '⊢bt' bt '∈' ft" := (valid_blocktype C bt ft).


(* ----------------------------------------------------------------- *)
(** *** Function Types *)
(** https://webassembly.github.io/multi-value/core/valid/types.html#function-types *)


Reserved Notation "'⊢ft' ft 'ok'" (at level 70).
Inductive valid_functype : functype -> Prop :=

  | VFT: forall ts1 ts2,
      ⊢ft ts1 --> ts2 ok

where "'⊢ft' ft 'ok' " := (valid_functype ft).
Hint Constructors valid_functype.


(* This is not explicitly defined but occured as

     (⊢ functype ok)*

*)
Reserved Notation "'⊢ft*' fts 'ok'" (at level 70).
Inductive valid_functypes : list functype -> Prop :=

  | VFTS: forall fts,
      Forall (fun ft => ⊢ft ft ok) fts ->
      ⊢ft* fts ok

where "'⊢ft*' fts 'ok' " := (valid_functypes fts).
Hint Constructors valid_functypes.


(* ----------------------------------------------------------------- *)
(** *** Table Types *)

Reserved Notation "'⊢tt' tt 'ok'" (at level 70).
Inductive valid_tabletype : tabletype -> Prop :=

  | VTT: forall limits elemtype,
      ⊢l limits ∈ I32.max ->      (* spec use literal [2^32] here *)
      ⊢tt (limits, elemtype) ok

where "'⊢tt' tt 'ok' " := (valid_tabletype tt).
Hint Constructors valid_tabletype.


(* ----------------------------------------------------------------- *)
(** *** Memory Types *)

Reserved Notation "'⊢mt' mt 'ok'" (at level 70).
Inductive valid_memtype : memtype -> Prop :=

  | VMT: forall limits,
      ⊢l limits ∈ I32.max16 ->      (* spec use literal [2^16] here *)
      ⊢mt limits ok

where "'⊢mt' mt 'ok' " := (valid_memtype mt).
Hint Constructors valid_memtype.

(* ----------------------------------------------------------------- *)
(** *** Global Types *)

Reserved Notation "'⊢gt' gt 'ok'" (at level 70).
Inductive valid_globaltype : globaltype -> Prop :=

  | VGT: forall mut vt,
      ⊢gt (mut, vt) ok

where "'⊢gt' gt 'ok' " := (valid_globaltype gt).
Hint Constructors valid_globaltype.

(* ----------------------------------------------------------------- *)
(** *** External Types *)

Reserved Notation "'⊢et' et 'ok'" (at level 70).
Inductive valid_externtype : externtype -> Prop :=

  | VET_func: forall ft,
      ⊢ft ft ok ->
      ⊢et (ET_func ft) ok

  | VET_table: forall tt,
      ⊢tt tt ok ->
      ⊢et (ET_table tt) ok

  | VET_mem: forall mt,
      ⊢mt mt ok ->
      ⊢et (ET_mem mt) ok

  | VET_global: forall gt,
      ⊢gt gt ok ->
      ⊢et (ET_global gt) ok

where "'⊢et' et 'ok' " := (valid_externtype et).
Hint Constructors valid_externtype.


(* ================================================================= *)
(** ** Instructions *)
(** https://webassembly.github.io/spec/core/valid/instructions.html *)

(** Instructions are classified by _function types_ [[t1∗] --> [t2∗]]
    that describe how they manipulate the _operand stack_.

    Typing extends to instruction sequences [instr∗]. Such a sequence
    has a function type [[t1∗] --> [t2∗]] if the _accumulative effect_
    of executing the instructions is consuming values of types [t1∗]
    off the operand stack and pushing new values of types [t2∗].
 *)


Reserved Notation "C '⊢' instr '∈' ft" (at level 70).
Reserved Notation "C '⊢*' instrs '∈' ft" (at level 70).

Inductive valid_instr : context -> instr -> functype -> Prop :=
(* ----------------------------------------------------------------- *)
(** *** Numeric Instruction *)

  | VI_const : forall C t val,
      t = type_of val ->
      C ⊢ val ∈ [] --> [t]

  | VI_unop : forall C t op,
      t = type_of op ->
      C ⊢ Unop op ∈ [t] --> [t]

  | VI_binop : forall C t op,
      t = type_of op ->
      C ⊢ Binop op ∈ [t; t] --> [t]

  | VI_testop : forall C t op,
      t = type_of op ->
      C ⊢ Testop op ∈ [t] --> [T_i32]

  | VI_relop : forall C t op,
      t = type_of op ->
      C ⊢ Relop op ∈ [t; t] --> [T_i32]
(*
  | VI_cvtop : forall C t1 t2 sx op,
      C ⊢ Cvtop t2 t1 sx op ∈ [t1] --> [t2]
*)

(* ----------------------------------------------------------------- *)
(** *** Parametric Instruction *)

  | VI_drop : forall C t,
      C ⊢ Drop ∈ [t] --> []

  | VI_select : forall C t,
      C ⊢ Select ∈ [t; t; T_i32] --> [t]

(* ----------------------------------------------------------------- *)
(** *** Variable Instruction *)

  (* | VI_local_get : forall C x t, *)
  (*     C.(C_locals).[x] = Some t -> *)
  (*     C ⊢ Local_get x ∈ [] --> [t] *)

  (* | VI_local_set : forall C x t, *)
  (*     C.(C_locals).[x] = Some t -> *)
  (*     C ⊢ Local_set x ∈ [t] --> [] *)

  (* | VI_local_tee : forall C x t, *)
  (*     C.(C_locals).[x] = Some t -> *)
  (*     C ⊢ Local_tee x ∈ [t] --> [t] *)

(*
  | VI_global_get : forall C x t,
      C.(globals).[x] = Some t ->
      C ⊢ Global_get x ∈ [] --> [t]

  | VI_global_set : forall C x t,
      C.(globals).[x] = Some t ->
      C ⊢ Global_set x ∈ [t] --> []
*)
   
(* ----------------------------------------------------------------- *)
(** *** Memory Instruction *)

(* ----------------------------------------------------------------- *)
(** *** Control Instructions *)

  | VI_nop : forall C,
      C ⊢ Nop ∈ [] --> []

  | VI_unreachable : forall C ts1 ts2,
      C ⊢ Unreachable ∈ ts1 --> ts2

  | VI_block : forall C bt ts1 ts2 instrs,
      C ⊢bt bt ∈ ts1 --> ts2 ->
      C,labels ts2 ⊢* instrs ∈ ts1 --> ts2 ->
      C ⊢ Block bt instrs ∈ ts1 --> ts2

  | VI_loop : forall C bt ts1 ts2 instrs,
      C ⊢bt bt ∈ ts1 --> ts2 ->
      C,labels ts1 ⊢* instrs ∈ ts1 --> ts2 ->
      C ⊢ Loop bt instrs ∈ ts1 --> ts2

  | VI_if : forall C bt ts1 ts2 instrs1 instrs2,
      C ⊢bt bt ∈ ts1 --> ts2 ->
      C,labels ts2 ⊢* instrs1 ∈ ts1 --> ts2 ->
      C,labels ts2 ⊢* instrs2 ∈ ts1 --> ts2 ->
      C ⊢ If bt instrs1 instrs2 ∈ (ts1 ++ [T_i32]) --> ts2

  | VI_br : forall C l ts ts1 ts2,
      C.(C_labels).[l] = Some ts ->
      C ⊢ Br l ∈ (ts1 ++ ts) --> ts2

  | VI_br_if : forall C l ts,
      C.(C_labels).[l] = Some ts ->
      C ⊢ Br_if l ∈ (ts ++ [T_i32]) --> ts

  | VI_br_table : forall C ls l__N ts ts1 ts2,
      Forall (fun l => C.(C_labels).[l] = Some ts) ls ->
      C.(C_labels).[l__N] = Some ts ->
      C ⊢ Br_table ls l__N ∈ (ts1 ++ ts ++ [T_i32]) --> ts2

  (* | VI_return : forall C tr ts1 ts2, *)
  (*     C.(C_return) = Some tr -> *)
  (*     C ⊢ Return ∈ (ts1 ++ tr) --> ts2 *)

  (* | VI_call : forall C x ts1 ts2, *)
  (*     C.(C_funcs).[x] = Some (ts1 --> ts2) -> *)
  (*     C ⊢ Call x ∈ ts1 --> ts2 *)

(*
  | VI_call_indirect : forall C x ts1 ts2,
      C.(tables).[0] = ??? ->
      C.(C_types).[x] = Some (ts1 --> ts2) ->
      C ⊢ [call_indirect x] ∈ (ts1 ++ [i32]) --> ts2
*)

(* ----------------------------------------------------------------- *)
(** *** Instruction Sequences *)
(** http://webassembly.github.io/spec/core/valid/instructions.html#instruction-sequences *)

with valid_instrs : context -> list instr -> functype -> Prop :=

  | VIS_empty : forall C ts,
      C ⊢* [] ∈ ts --> ts

  | VIS_snoc : forall C instrs instr__N ts0 ts1 ts ts3,
      C ⊢* instrs ∈ ts1 --> (ts0 ++ ts) (* ts2 *) ->
      C ⊢  instr__N ∈ ts --> ts3 ->
      C ⊢* instrs ++ [instr__N] ∈ ts1 --> (ts0 ++ ts3)

where "C '⊢' instr '∈' ft" := (valid_instr C instr ft)
  and "C '⊢*' instrs '∈' ft" := (valid_instrs C instrs ft).

Hint Constructors valid_instr.
Hint Constructors valid_instrs.


(* postpone functional type checking.

Fixpoint check_instr 

*)



(* ----------------------------------------------------------------- *)
(** *** Expressions *)
(** http://webassembly.github.io/spec/core/valid/instructions.html#expressions *)

(** expression, a.k.a block is almost the same as [list instr]
    except it is typechecking against the [resulttype] rather than [functype].

    so we need this rule to establish the relation between them.
 *)

Reserved Notation "C '⊢e' expr '∈' ty" (at level 70).
Inductive valid_expr : context -> expr -> resulttype -> Prop :=

  | VE : forall C e tr,
      C ⊢* e ∈ [] --> tr ->
      C ⊢e e ∈ tr

where "C '⊢e' expr '∈' ty" := (valid_expr C expr ty).

Hint Constructors valid_expr.


(** **** Constant Expressions *)
(** http://webassembly.github.io/spec/core/valid/instructions.html#constant-expressions *)

(** the spec said:

    > In a constant expression [instr* 𝖾𝗇𝖽] all instructions in [instr*] must be constant.

    so which extract the [instr*] from [expr] without defining a [Inductive const_instrs].
 *)

Reserved Notation "C '⊢e' instrs 'const'" (at level 70).
Reserved Notation "C '⊢' instr 'const'" (at level 70).
Inductive const_expr : context -> expr -> Prop :=

  | CE: forall C e,
      Forall (fun instr => C ⊢ instr const) e ->
      C ⊢e e const

with const_instr : context -> instr -> Prop :=

  | CI_const : forall C v,
      C ⊢ Const v const

  (* | CI_global_get *)

where "C '⊢e' e 'const' " := (const_expr C e)
  and "C '⊢' instr 'const' " := (const_instr C instr).
    
Hint Constructors const_expr.
Hint Constructors const_instr.


(** **** Constant Expressions - Lemma *)
(** To get [val] back from [instr], we need boolean operations. 
    Naming conventions follow the Coq standard lib that postfix with a [b]
*)

Section ConstLemma.

  Definition const_b (i: instr) : bool := 
    match i with
    | Const _ => true
    | _ => false
    end.

  Definition consts_b (instrs: list instr) : bool :=
    forallb const_b instrs.

  Lemma const_eqbP : forall instr C,
      reflect (C ⊢ instr const) (const_b instr).
  Proof.
    intros.
    apply iff_reflect. split; intros.
    - (* -> *)
      destruct instr;
        try (inversion H).
      reflexivity.
    - (* <- *)
      destruct instr;
        try (inversion H). 
      constructor.
  Qed.

  Lemma consts_eqbP : forall e C,
      reflect (C ⊢e e const) (consts_b e).
  Proof with auto.
    intros.
    apply iff_reflect. split; intros.
    - (* -> *)
      inverts H.
      induction e.
      + (* [] *) simpl...
      + (* :: *)
        simpl. 
        apply andb_true_iff.
        split.
        ++ (* head *)
          apply Forall_inv in H0.
          destruct (const_eqbP a C)...
        ++ (* tail *)
          apply Forall_inv_tail in H0.
          apply IHe...
    - (* <- *)
      induction e.
      + (* [] *) constructor. apply Forall_nil.
      + (* :: *)
        simpl in H.
        apply andb_true_iff in H.
        destruct H.
        constructor.
        constructor.
        ++ destruct (const_eqbP a C). auto. inverts H.
        ++ apply IHe in H0. inverts H0...
  Qed.

  Lemma const_val : forall instr C,
      C ⊢ instr const ->
      exists val, instr = Const val.
  Proof with auto.
    introv H.
    destruct instr;
      try (inversion H); subst.
    exists val...
  Qed.

  Lemma consts_vals : forall e C,
      C ⊢e e const ->
      exists vals, e = map Const vals.
  Proof with auto.
    introv H.
    induction e.
    - exists (@nil val)...
    - inverts H.
      inverts H0.
      assert (C ⊢e e const). constructor. assumption.
      apply IHe in H.
      destruct H.
      apply const_val in H2.
      destruct H2; subst.
      exists (x0 :: x). simpl...
  Qed.

End ConstLemma.

(* postpone functional type checking.

Fixpoint check_expr (C : context) (e : expr) (tr : resulttype) :=

*)



(* ================================================================= *)
(** ** Modules *)
(** http://webassembly.github.io/spec/core/valid/modules.html *)

(* ----------------------------------------------------------------- *)
(** *** Functions *)
(** http://webassembly.github.io/spec/core/valid/modules.html#functions *)

(** Issue on "validation rule for function is inaccurate"
  * https://github.com/WebAssembly/spec/issues/1072
  *)

Reserved Notation "C '⊢f' f ∈ ft" (at level 70).
Inductive valid_func : context -> func -> functype -> Prop :=

  | VF : forall C x ts expr ts1 ts2,
      C.(C_types).[x] = Some (ts1 --> ts2) ->
      C with_locals = (ts1 ++ ts) with_labels = [ts2] with_return = Some ts2 ⊢e expr ∈ ts2 ->
      C ⊢f {| F_type := x; F_locals := ts; F_body := expr |} ∈ ts1 --> ts2

where "C '⊢f' f ∈ ft" := (valid_func C f ft).
Hint Constructors valid_functypes.

(* This is not explicitly defined but occured as

     (⊢ func : ft)*

   when typing modules as a pairwise relation.

   > Let ft∗ be the concatenation of the internal function types fti, in index order.
*)

Reserved Notation "C '⊢f*' fs ∈ fts" (at level 70).
Inductive valid_funcs : context -> list func -> list functype -> Prop :=

  | VFS: forall C fs fts,
      Forall2 (fun func ft => C ⊢f func ∈ ft) fs fts ->  
      C ⊢f* fs ∈ fts

where "C '⊢f*' fs ∈ fts" := (valid_funcs C fs fts).
Hint Constructors valid_funcs.


Module FuncTyTest.

  Definition ft := [T_i32] --> [T_i32].
  Definition ins :=
    let '(ins --> outs) := ft in ins.
  Definition ins2 :=
    match ft with
    | (ins --> outs) => ins
    end.

  Definition foo := Build_func 0 [] []. 
  Definition a :=
    (* By let pattern *)
    let 'Build_func a b c := foo in a.
  Definition a2 :=
    (* By constructor pattern *)
    match foo with
      | Build_func a b c  => a
    end.
  Definition a3 :=
    (* By notational pattern *)
    match foo with
      | {| F_type := a; F_locals := b; F_body := c |} => a
    end.

End FuncTyTest.

(* postpone functional type checking.

Fixpoint check_func (C: context) (f: func) :=
  let '(Build_func type locals body) := f in
  let '(ts1 --> ts2) := C.(C_types).[type] in
  let C' = C, locals__s (ts1 ++ ts), labels ts2 with_return = Some ts2 in
  check_expr C' body ts2.
*)


(* ----------------------------------------------------------------- *)
(** *** Tables *)

Reserved Notation "C '⊢t' t ∈ tt" (at level 70).
Inductive valid_table : context -> table -> tabletype -> Prop :=

  | VT : forall C tt,
      ⊢tt tt ok ->
      C ⊢t {| T_type := tt |} ∈ tt

where "C '⊢t' t ∈ tt" := (valid_table C t tt).
Hint Constructors valid_table.

(* This is not explicitly defined but occured as

     (⊢ table : tt)*

   when typing modules as a pairwise relation.

   > Let tt∗ be the concatenation of the internal table types tti, in index order.
*)

Reserved Notation "C '⊢t*' tabs ∈ tts" (at level 70).
Inductive valid_tables : context -> list table -> list tabletype -> Prop :=

  | VTS: forall C tabs tts,
      Forall2 (fun table tt => C ⊢t table ∈ tt) tabs tts ->
      C ⊢t* tabs ∈ tts

where "C '⊢t*' tabs '∈' tts" := (valid_tables C tabs tts).
Hint Constructors valid_tables.


(* ----------------------------------------------------------------- *)
(** *** Modules *)
(** http://webassembly.github.io/spec/core/valid/modules.html#valid-module *)

(** A module is entirely closed, i.e., no initial context is required.
    Instead, the context C for validation of the module’s content is constructed from the definitions in the module. *)

(** Let ft∗ be the concatenation of the internal function types fti, in index order.
 *)

Reserved Notation "'⊢' M ∈ ty" (at level 70).
Inductive valid_module: module -> functype -> Prop :=
  | VM : forall its ets fts tts functypes funcs tables,

(* Let C be a context where: *)
      let
        C := {|
          C_types := functypes;
          C_funcs := fts;  (* ++ ifts *)
          C_tables := tts; (* ++ itts *)
          C_locals := [];
          C_labels := [];
          C_return := None;
        |}
      in

      (* N.B. this has been removed in multi-value *)
        ⊢ft* functypes ok ->

      C ⊢f* funcs ∈ fts ->
      C ⊢t* tables ∈ tts ->

      (* length limitatin of current Wasm version *)
      length C.(C_tables) <= 1 ->
      (* length C.(C_mems) <= 1 -> *)

      ⊢ {|
           M_types := functypes;
           M_funcs := funcs;
           M_tables := tables;
        |} ∈ its --> ets
      
where "'⊢' M ∈ ty" := (valid_module M ty).


(* postpone functional type checking.

Fixpoint prepass_funcs (funcs : list func) : list functype :=
  map (fun func => C.(C_types).[func.type]) funcs. 

Fixpoint check_module 

*)
