(* ***************************************************************** *)
(* Validation.v                                                      *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)


(* ################################################################# *)
(** * Validation *)

From Wasm Require Export Structure.
From Coq Require Export Structures.Equalities.
Import FunctypeNotations.

(* Test imports/exports *)

Module ImportExportTests.
Definition ex_fun_nu : functype := [] --> [T_i32].
Definition ex_fun_nu_ty_c : ty := [] --> [T_i32].
Print ex_fun_nu.
Print ex_fun_nu_ty_c.
Print ty.
Print module.
End ImportExportTests.


(* ================================================================= *)
(** ** Conventions *)

(* ----------------------------------------------------------------- *)
(** *** Contexts *)

Record contexts :=
  {
    types : list functype;
    funcs : list functype;
    locals : list valtype;
    labels : list resulttype;
    return' : option resulttype;
  }.

Notation idx := nth_error.

Notation "l '.[' x ]" :=
  (idx l x)
  (at level 60, right associativity) : wasm_scope.

Definition replace_labels (C: contexts) (xs: list resulttype) :=
  {|
    types := C.(types);
    funcs := C.(funcs);
    locals := C.(locals);
    labels := xs;
    return' := C.(return');
  |}.

Definition cons_labels (C: contexts) (x: resulttype) :=
  {|
    types := C.(types);
    funcs := C.(funcs);
    locals := C.(locals);
    labels := x :: C.(labels);
    return' := C.(return');
  |}.

Notation "{ C 'with' 'labels' = x }" := (replace_labels C x).

Notation "C ',' 'labels' x" :=
  (cons_labels C x)
  (at level 69, left associativity) : wasm_scope.

Module ContextTests.

  (* nth is total and require default *)
  Compute (nth 1 [1;2;3] 0).
  Compute (idx [1;2;3] 1).

  Definition ex_C :=
    {|
      types := [];
      funcs := [];
      locals := [T_i32; T_i32];
      labels := [];
      return' := None;
    |}.

  Compute (idx ex_C.(locals) 0).
  Compute (idx ex_C.(locals) 1).
  Compute (idx ex_C.(locals) 2).

  (* Testing Updates Notation *)
  Definition ex_C2 := { ex_C with labels = [[T_i32]] }.
  Compute ex_C2.

  (* Testing Field Cons Notation *)
  Definition ex_C3 := ex_C, labels [T_i32]. 
  Compute ex_C3.

  Definition ex_C4 := ex_C, labels [T_f32], labels [T_i32]. 
  Compute ex_C4.

  (* Testing Indexing Notation *)
  Compute ([1;2;3].[1] ).

  Compute (ex_C.(locals).[0]).
  Compute (ex_C.(locals).[1]).
  Compute (ex_C.(locals).[2]).

  Compute (forallb (fun ty => eqb_valtype ty T_i32) ex_C.(locals)).
  Compute (all_valtype ex_C.(locals) T_i32).

  Check Forall.
  Definition all_i32 := Forall (fun ty => ty = T_i32) (locals ex_C).
  Lemma ex_forall : all_i32.
  Proof with eauto.
    unfold all_i32.
    simpl.
    eapply Forall_cons...
  Qed.



(* ================================================================= *)
(** ** Types *)

Inductive valid_ty : ty -> Prop := .


(* ================================================================= *)
(** ** Instructions *)
(** https://webassembly.github.io/spec/core/valid/instructions.html#instructions *)

(** Instructions are classified by _function types_ [[t1∗] --> [t2∗]]
    that describe how they manipulate the _operand stack_.

    Typing extends to instruction sequences [instr∗]. Such a sequence
    has a function type [[t1∗] --> [t2∗]] if the _accumulative effect_
    of executing the instructions is consuming values of types [t1∗]
    off the operand stack and pushing new values of types [t2∗].
 *)

Reserved Notation "C '⊢' instr '∈' ty" (at level 70).
Reserved Notation "C '⊢s' instrs '∈' ty" (at level 70).

Inductive valid_instr : contexts -> instr -> functype -> Prop :=
(* ----------------------------------------------------------------- *)
(** *** Numeric Instruction *)

  | VI_const : forall C t c,
      C ⊢ const t c ∈ [] --> [t]

  | VI_iunop : forall C t op,
      C ⊢ iunop t op ∈ [t] --> [t]

  | VI_ibinop : forall C t op,
      C ⊢ ibinop t op ∈ [t; t] --> [t]

  | VI_itestop : forall C t op,
      C ⊢ itestop t op ∈ [t] --> [T_i32]

  | VI_irelop : forall C t op,
      C ⊢ irelop t op ∈ [t; t] --> [T_i32]
(*
  | VI_cvtop : forall C t1 t2 sx op,
      C ⊢ cvtop t2 t1 sx op ∈ [t1] --> [t2]
*)

(* ----------------------------------------------------------------- *)
(** *** Parametric Instruction *)

  | VI_drop : forall C t,
      C ⊢ drop ∈ [t] --> []

  | VI_select : forall C t,
      C ⊢ select ∈ [t; t; T_i32] --> [t]

(* ----------------------------------------------------------------- *)
(** *** Variable Instruction *)

  | VI_local_get : forall C x t,
      C.(locals).[x] = Some t ->
      C ⊢ local_get x ∈ [] --> [t]

  | VI_local_set : forall C x t,
      C.(locals).[x] = Some t ->
      C ⊢ local_set x ∈ [t] --> []

  | VI_local_tee : forall C x t,
      C.(locals).[x] = Some t ->
      C ⊢ local_tee x ∈ [t] --> [t]

(*
  | VI_global_get : forall C x t,
      C.(globals).[x] = Some t ->
      C ⊢ global_get x ∈ [] --> [t]

  | VI_global_set : forall C x t,
      C.(globals).[x] = Some t ->
      C ⊢ global_set x ∈ [t] --> []
*)
   
(* ----------------------------------------------------------------- *)
(** *** Memory Instruction *)

(* ----------------------------------------------------------------- *)
(** *** Control Instructions *)

  | VI_nop : forall C,
      C ⊢ nop ∈ [] --> []

  | VI_unreachable : forall C ts1 ts2,
      C ⊢ unreachable ∈ ts1 --> ts2

  | VI_block : forall C tr instrs,
      C, labels tr ⊢s instrs ∈ [] --> tr ->
      C ⊢ block tr instrs ∈ [] --> tr

  | VI_loop : forall C tr instrs,
      C, labels [] ⊢s instrs ∈ [] --> tr ->
      C ⊢ loop tr instrs ∈ [] --> tr

  | VI_if : forall C tr instrs1 instrs2,
      C, labels tr ⊢s instrs1 ∈ [] --> tr ->
      C, labels tr ⊢s instrs2 ∈ [] --> tr ->
      C ⊢ if' tr instrs1 instrs2 ∈ [T_i32] --> tr

  | VI_br : forall C l tr ts1 ts2,
      C.(labels).[l] = Some tr ->
      C ⊢ br l ∈ (ts1 ++ tr) --> ts2

  | VI_br_if : forall C l tr, 
      C.(labels).[l] = Some tr ->
      C ⊢ br_if l ∈ (tr ++ [T_i32]) --> tr

  | VI_br_table : forall C ls l__N tr ts1 ts2, 
      (* this might be easier via length check *)
      Forall (fun l => C.(labels).[l] <> None) ls ->
      C.(labels).[l__N] = Some tr ->
      C ⊢ br_table ls l__N ∈ (ts1 ++ tr ++ [T_i32]) --> ts2

  | VI_return : forall C tr ts1 ts2,
      C.(return') = Some tr ->
      C ⊢ Structure.return' ∈ (ts1 ++ tr) --> ts2

  | VI_call : forall C x ts1 ts2,
      C.(funcs).[x] = Some (ts1 --> ts2) ->
      C ⊢ call x ∈ ts1 --> ts2

(*
  | VI_call_indirect : forall C x ts1 ts2,
      C.(tables).[0] = ??? ->
      C.(types).[x] = Some (ts1 --> ts2) ->
      C ⊢ [call_indirect x] ∈ (ts1 ++ [i32]) --> ts2
*)

(* ----------------------------------------------------------------- *)
(** *** Instruction Sequences *)
(** http://webassembly.github.io/spec/core/valid/instructions.html#instruction-sequences *)

with valid_instrs : contexts -> list instr -> functype -> Prop :=
  | VIS_empty : forall C ts,
      C ⊢s [] ∈ ts --> ts

  | VIS_snoc : forall C instrs instr__N ts0 ts1 ts ts3,
      C ⊢ instr__N ∈ ts --> ts3 ->
      C ⊢s instrs ∈ ts1 --> (ts0 ++ ts) ->
      C ⊢s instrs ++ [instr__N] ∈ ts1 --> (ts0 ++ ts3)

where "C '⊢' instr '∈' ty" := (valid_instr C instr ty)
  and "C '⊢s' instrs '∈' ty" := (valid_instrs C instrs ty).

Hint Constructors valid_instr.
Hint Constructors valid_instrs.


(* ----------------------------------------------------------------- *)
(** *** Expressions *)
(** http://webassembly.github.io/spec/core/valid/instructions.html#expressions *)

Reserved Notation "C '⊢e' expr '∈' ty" (at level 70).
Inductive valid_expr : contexts -> expr -> resulttype -> Prop :=

  | VE : forall C e tr,
      C ⊢s e ∈ [] --> tr ->
      C ⊢e e ∈ tr

where "C '⊢e' expr '∈' ty" := (valid_expr C expr ty).

Hint Constructors valid_expr.


(** **** Constant Expressions *)
(** http://webassembly.github.io/spec/core/valid/instructions.html#constant-expressions *)

(** the spec :

        In a constant expression instr∗ 𝖾𝗇𝖽 all instructions in instr∗ must be constant.

    implicitly fetch the internal instr list from expr without the need of defining [const_instrs]
 *)

Reserved Notation "C '⊢e' instrs 'const'" (at level 70).
Reserved Notation "C '⊢' instr 'const'" (at level 70).
Inductive const_expr : contexts -> expr -> Prop :=

  | CE: forall C e,
      Forall (fun instr => C ⊢ instr const) e ->
      C ⊢e e const

with const_instr : contexts -> instr -> Prop :=

  | CI_const : forall C t c,
      C ⊢ Structure.const t c const

where "C '⊢e' e 'const' " := (const_expr C e)
  and "C '⊢' instr 'const' " := (const_instr C instr).
    
Hint Constructors const_expr.
Hint Constructors const_instr.

