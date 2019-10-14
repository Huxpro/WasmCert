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
Print ex_fun_nu.
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
    C_locals : list valtype;
    C_labels : list resulttype;

    (* this could actually be just a resulttype since [] can represent None *)
    C_return : option resulttype;  
  }.

Definition empty_context :=
  {|
    C_types := [];
    C_funcs := [];
    C_tables := [];
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
  (at level 69, left associativity) : wasm_scope.

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
  (at level 69, left associativity) : wasm_scope.

Definition replace_return (C: context) (x: resulttype) :=
  {|
    C_return:= Some x;
    C_types := C.(C_types);
    C_funcs := C.(C_funcs);
    C_tables := C.(C_tables);
    C_locals := C.(C_locals);
    C_labels := C.(C_labels);
  |}.
Notation "C 'with_return' = x" :=
  (replace_return C x)
  (at level 69, left associativity) : wasm_scope.


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
  (at level 68, left associativity) : wasm_scope.


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
  (at level 68, left associativity) : wasm_scope.



(** Tests *)

Module ContextTests.

  (* nth is total and require default *)
  Compute (nth 1 [1;2;3] 0).
  Compute (idx [1;2;3] 1).

  Example ex_C :=
    {|
      C_types := [];
      C_funcs := [];
      C_tables := [];
      C_locals := [T_i32; T_i32];
      C_labels := [];
      C_return := None;
    |}.

  Compute (idx ex_C.(C_locals) 0).
  Compute (idx ex_C.(C_locals) 1).
  Compute (idx ex_C.(C_locals) 2).

  (* Testing Updates Notation *)
  Example ex_Crl := ex_C with_labels = [[T_i32]].
  Compute ex_Crl.

  Example ex_Crr := ex_C with_return = [T_i32].
  Compute ex_Crr.

  Example ex_Crlr := ex_C with_locals = [T_i32] with_return = [T_i32].
  Compute ex_Crlr.

  (* Testing if break pair *)
  Example pair1 := (1,2).
  Example pair2 := (1, 2).

  (* Testing Field Cons Notation *)
  Example ex_Cc1 := ex_C,labels [T_i32]. 
  Compute ex_Cc1.

  Example ex_Cc2 := ex_C,labels [T_f32],labels [T_i32]. 
  Compute ex_Cc2.

  (* Testing associativity *)
  Example ex_Ca1 := ex_C ,labels [T_f32] ,labels [T_i32] with_return = [T_i32].
  Compute ex_Ca1.

  (* Testing Indexing Notation *)
  Compute ([1;2;3].[1] ).

  Compute (ex_C.(C_locals).[0]).
  Compute (ex_C.(C_locals).[1]).
  Compute (ex_C.(C_locals).[2]).

  Compute (forallb (fun ty => eqb_valtype ty T_i32) ex_C.(C_locals)).
  Compute (all_valtype ex_C.(C_locals) T_i32).

  Check Forall.
  Example all_i32 := Forall (fun ty => ty = T_i32) (C_locals ex_C).

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
(** *** Limits *)

Reserved Notation "'⊢l' l '∈' k" (at level 70).
Inductive valid_limit : limits -> I32.t -> Prop :=

  (* No max limits *)

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

(* ----------------------------------------------------------------- *)
(** *** Global Types *)

(* ----------------------------------------------------------------- *)
(** *** External Types *)


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
Reserved Notation "C '⊢*' instrs '∈' ty" (at level 70).


Inductive valid_instr : context -> instr -> functype -> Prop :=
(* ----------------------------------------------------------------- *)
(** *** Numeric Instruction *)

  | VI_const : forall C t v,
      t = type_of v ->
      C ⊢ Const v ∈ [] --> [t]

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

  | VI_local_get : forall C x t,
      C.(C_locals).[x] = Some t ->
      C ⊢ Local_get x ∈ [] --> [t]

  | VI_local_set : forall C x t,
      C.(C_locals).[x] = Some t ->
      C ⊢ Local_set x ∈ [t] --> []

  | VI_local_tee : forall C x t,
      C.(C_locals).[x] = Some t ->
      C ⊢ Local_tee x ∈ [t] --> [t]

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

  | VI_loop : forall C bt ta tr instrs,
      C ⊢bt bt ∈ ta --> tr ->
      C,labels ta ⊢* instrs ∈ ta --> tr ->
      C ⊢ Loop bt instrs ∈ ta --> tr

  | VI_if : forall C bt ta tr instrs1 instrs2,
      C ⊢bt bt ∈ ta --> tr ->
      C,labels tr ⊢* instrs1 ∈ ta --> tr ->
      C,labels tr ⊢* instrs2 ∈ ta --> tr ->
      C ⊢ If bt instrs1 instrs2 ∈ (ta ++ [T_i32]) --> tr

  | VI_br : forall C l tr ts1 ts2,
      C.(C_labels).[l] = Some tr ->
      C ⊢ Br l ∈ (ts1 ++ tr) --> ts2

  | VI_br_if : forall C l tr, 
      C.(C_labels).[l] = Some tr ->
      C ⊢ Br_if l ∈ (tr ++ [T_i32]) --> tr

  | VI_br_table : forall C ls l__N tr ts1 ts2, 
      (* this might be easier via length check *)
      Forall (fun l => C.(C_labels).[l] <> None) ls ->
      C.(C_labels).[l__N] = Some tr ->
      C ⊢ Br_table ls l__N ∈ (ts1 ++ tr ++ [T_i32]) --> ts2

  | VI_return : forall C tr ts1 ts2,
      C.(C_return) = Some tr ->
      C ⊢ Return ∈ (ts1 ++ tr) --> ts2

  | VI_call : forall C x ts1 ts2,
      C.(C_funcs).[x] = Some (ts1 --> ts2) ->
      C ⊢ Call x ∈ ts1 --> ts2

(*
  | VI_call_indirect : forall C x ts1 ts2,
      C.(tables).[0] = ??? ->
      C.(C_types).[x] = Some (ts1 --> ts2) ->
      C ⊢ [call_indirect x] ∈ (ts1 ++ [i32]) --> ts2
*)

(* ----------------------------------------------------------------- *)
(** *** Instruction Sequences *)
(** http://webassembly.github.io/spec/core/valid/instructions.html#instruction-sequences *)

with valid_seq : context -> list instr -> functype -> Prop :=
  | VIS_empty : forall C ts,
      C ⊢* [] ∈ ts --> ts

  | VIS_snoc : forall C instrs instr__N ts0 ts1 ts ts3,
      C ⊢ instr__N ∈ ts --> ts3 ->
      C ⊢* instrs ∈ ts1 --> (ts0 ++ ts) ->
      C ⊢* instrs ++ [instr__N] ∈ ts1 --> (ts0 ++ ts3)

where "C '⊢' instr '∈' ty" := (valid_instr C instr ty)
  and "C '⊢*' instrs '∈' ty" := (valid_seq C instrs ty).

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
      C ⊢* e ∈ [] --> tr ->
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

  | CI_const : forall C v,
      C ⊢ Const v const

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

Reserved Notation "C '⊢f' f ∈ ft" (at level 70).
Inductive valid_func : context -> func -> functype -> Prop :=

  | VF : forall C x ts expr ts1 ts2,
      C.(C_types).[x] = Some (ts1 --> ts2) ->
      C with_locals = (ts1 ++ ts) with_labels = [ts2] with_return = ts2 ⊢e expr ∈ ts2 ->
      C ⊢f {| F_type := x; F_locals := ts; F_body := expr |} ∈ ts1 --> ts2

where "C '⊢f' f ∈ ft" := (valid_func C f ft).


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
  let C' = C, locals__s (ts1 ++ ts), labels ts2 with_return = ts2 in
  check_expr C' body ts2.
*)


(* ----------------------------------------------------------------- *)
(** *** Tables *)

Reserved Notation "C '⊢t' t ∈ tt" (at level 70).
Inductive valid_table : context -> table -> tabletype -> Prop :=

  | VT : forall C tablety,
      ⊢tt tablety ok ->
      C ⊢t {| T_type := tablety |} ∈ tablety

where "C '⊢t' t ∈ tt" := (valid_table C t tt).


(* ----------------------------------------------------------------- *)
(** *** Modules *)
(** http://webassembly.github.io/spec/core/valid/modules.html#valid-module *)

(** A module is entirely closed, i.e., no initial context is required.
    Instead, the context C for validation of the module’s content is constructed from the definitions in the module. *)

(** Let ft∗ be the concatenation of the internal function types fti, in index order.
 *)

Reserved Notation "'⊢' M ∈ ty" (at level 70).
Inductive valid_module: module -> functype -> Prop :=
  | VM : forall M its ets fts ts,
      let
        C := {|
          C_types := M.(M_types);
          C_funcs := fts;
          C_tables := ts;
          C_locals := [];
          C_labels := [];
          C_return := None;
        |}
      in
      (* this has been removed in multi-value *)
      Forall (fun functype => ⊢ft functype ok) M.(M_types) ->

      (* pairwise related *)
      Forall2 (fun func ft => C ⊢f func ∈ ft) M.(M_funcs) fts ->  

      Forall (fun table => C ⊢t table ∈ table.(T_type)) M.(M_tables) ->

      ⊢ M ∈ its --> ets
      
where "'⊢' M ∈ ty" := (valid_module M ty).


(* postpone functional type checking.

Fixpoint prepass_funcs (funcs : list func) : list functype :=
  map (fun func => C.(C_types).[func.type]) funcs. 

Fixpoint check_module 

*)
