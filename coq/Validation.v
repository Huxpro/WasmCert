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
(** http://webassembly.github.io/spec/core/valid/conventions.html *)

(* ----------------------------------------------------------------- *)
(** *** Contexts *)
(** http://webassembly.github.io/spec/core/valid/conventions.html#contexts *)

Record context :=
  {
    types : list functype;
    funcs : list functype;
    locals : list valtype;
    labels : list resulttype;
    return' : option resulttype;
  }.


(** indexing and indexing notation *)

Notation idx := nth_error.
Notation "l '.[' x ]" :=
  (idx l x)
  (at level 60, right associativity) : wasm_scope.


(** functional update - replacing fields *)

Definition replace_labels (C: context) (xs: list resulttype) :=
  {|
    types := C.(types);
    funcs := C.(funcs);
    locals := C.(locals);
    labels := xs;
    return' := C.(return');
  |}.
Notation "C 'with_labels' = x" :=
  (replace_labels C x)
  (at level 69, left associativity) : wasm_scope.

Definition replace_return (C: context) (x: resulttype) :=
  {|
    types := C.(types);
    funcs := C.(funcs);
    locals := C.(locals);
    labels := C.(labels);
    return' := Some x;
  |}.
Notation "C 'with_return' = x" :=
  (replace_return C x)
  (at level 69, left associativity) : wasm_scope.


(** functional update - cons on fields *)

Definition cons_labels (C: context) (x: resulttype) :=
  {|
    types := C.(types);
    funcs := C.(funcs);
    locals := C.(locals);
    labels := x :: C.(labels);
    return' := C.(return');
  |}.
Notation "C ',' 'labels' x" :=
  (cons_labels C x)
  (at level 68, left associativity) : wasm_scope.


Definition cons_locals (C: context) (x: valtype) :=
  {|
    types := C.(types);
    funcs := C.(funcs);
    locals := x :: C.(locals);
    labels := C.(labels);
    return' := C.(return');
  |}.
Notation "C ',' 'locals' x" :=
  (cons_locals C x)
  (at level 68, left associativity) : wasm_scope.


(** functional update - prepend on fields *)

Definition prepend_locals (C: context) (xs: list valtype) :=
  {|
    types := C.(types);
    funcs := C.(funcs);
    locals := xs ++ C.(locals);
    labels := C.(labels);
    return' := C.(return');
  |}.
Notation "C ',' 'locals__s' xs" :=
  (prepend_locals C xs)
  (at level 68, left associativity) : wasm_scope.

(** Tests *)

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
  Definition ex_C2 := ex_C with_labels = [[T_i32]].
  Compute ex_C2.

  Definition ex_Cr := ex_C with_return = [T_i32].
  Compute ex_Cr.

  (* Testing Field Cons Notation *)
  Definition ex_C3 := ex_C, labels [T_i32]. 
  Compute ex_C3.

  Definition ex_C4 := ex_C, labels [T_f32], labels [T_i32]. 
  Compute ex_C4.

  Definition ex_C5 := ex_C, locals__s [T_f32; T_f32].
  Compute ex_C5.

  Definition ex_C6 := ex_C, labels [T_f32], labels [T_i32] with_return = [T_i32].
  Compute ex_C6.

  Definition ex_C7 := ex_C, labels [T_f32], locals__s [T_i32; T_i32] with_return = [T_i32].
  Compute ex_C7.

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

End ContextTests.



(* ================================================================= *)
(** ** Types *)
(** http://webassembly.github.io/spec/core/valid/types.html *)


(* ----------------------------------------------------------------- *)
(** *** Function Types *)
(** http://webassembly.github.io/spec/core/valid/types.html#function-types *)

(** The arity m must not be larger than 1.
    The restriction to at most one result may be removed in future versions of WebAssembly.
 *)

Reserved Notation "'⊢ft' ft 'ok'" (at level 70).
Inductive valid_functype : functype -> Prop :=
  | VFT: forall ts1 ts2,
      length ts2 <= 1 ->
      ⊢ft ts1 --> ts2 ok
where "'⊢ft' ft 'ok' " := (valid_functype ft).

Hint Constructors valid_functype.




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

Reserved Notation "C '⊢' instr '∈' ty" (at level 70).
Reserved Notation "C '⊢s' instrs '∈' ty" (at level 70).

Inductive valid_instr : context -> instr -> functype -> Prop :=
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

with valid_seq : context -> list instr -> functype -> Prop :=
  | VIS_empty : forall C ts,
      C ⊢s [] ∈ ts --> ts

  | VIS_snoc : forall C instrs instr__N ts0 ts1 ts ts3,
      C ⊢ instr__N ∈ ts --> ts3 ->
      C ⊢s instrs ∈ ts1 --> (ts0 ++ ts) ->
      C ⊢s instrs ++ [instr__N] ∈ ts1 --> (ts0 ++ ts3)

where "C '⊢' instr '∈' ty" := (valid_instr C instr ty)
  and "C '⊢s' instrs '∈' ty" := (valid_seq C instrs ty).

Hint Constructors valid_instr.
Hint Constructors valid_seq.


(* postpone functional type checking.

Fixpoint check_instr 

*)




(* ----------------------------------------------------------------- *)
(** *** Expressions *)
(** http://webassembly.github.io/spec/core/valid/instructions.html#expressions *)

(** a.k.a Block *)

Reserved Notation "C '⊢e' expr '∈' ty" (at level 70).
Inductive valid_expr : context -> expr -> resulttype -> Prop :=

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
Inductive const_expr : context -> expr -> Prop :=

  | CE: forall C e,
      Forall (fun instr => C ⊢ instr const) e ->
      C ⊢e e const

with const_instr : context -> instr -> Prop :=

  | CI_const : forall C t c,
      C ⊢ Structure.const t c const

where "C '⊢e' e 'const' " := (const_expr C e)
  and "C '⊢' instr 'const' " := (const_instr C instr).
    
Hint Constructors const_expr.
Hint Constructors const_instr.


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

Reserved Notation "C '⊢f' f ∈ ty" (at level 70).
Inductive valid_func : context -> func -> functype -> Prop :=

  | VF : forall C (f: func) x ts expr ts1 ts2,
      C.(types).[x] = Some (ts1 --> ts2) ->
      C, locals__s (ts1 ++ ts), labels ts2 with_return = ts2 ⊢e expr ∈ ts2 ->
      C ⊢f {| type := x; Structure.locals := ts; body := expr |} ∈ ts1 --> ts2

where "C '⊢f' f ∈ ty" := (valid_func C f ty).

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
    | {| type := a; Structure.locals := b; body := c |} => a
  end.

(* postpone functional type checking.

Fixpoint check_func (C: context) (f: func) :=
  let '(Build_func type locals body) := f in
  let '(ts1 --> ts2) := C.(types).[type] in
  let C' = C, locals__s (ts1 ++ ts), labels ts2 with_return = ts2 in
  check_expr C' body ts2.
*)



(* ----------------------------------------------------------------- *)
(** *** Modules *)
(** http://webassembly.github.io/spec/core/valid/modules.html#valid-module *)

(** A module is entirely closed, i.e., no initial context is required.
    Instead, the context C for validation of the module’s content is constructed from the definitions in the module. *)

(** Let ft∗ be the concatenation of the internal function types fti, in index order.
 *)


Reserved Notation "'⊢' module ∈ ty" (at level 70).
Inductive valid_module: module -> functype -> Prop :=
  | VM : forall (m: module) its ets fts ft,
      let
        C : context := {|
          types := m.(Structure.types);
          funcs := fts;
          locals := [];
          labels := [];
          return' := None;
        |}
      in
      Forall (fun functype => ⊢ft functype ok) m.(Structure.types) ->
      Forall (fun func => C ⊢f func ∈ ft) m.(Structure.funcs) ->
      ⊢ m ∈ its --> ets
      
where "'⊢' m ∈ ty" := (valid_module m ty).


(* postpone functional type checking.

Fixpoint prepass_funcs (funcs : list func) : list functype :=
  map (fun func => C.(types).[func.type]) funcs. 

Fixpoint check_module 

*)