
(* ***************************************************************** *)
(* Execution.v                                                       *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)


(* ################################################################# *)
(** * Execution *)

From Wasm Require Export Structure.
From Wasm Require Export Numerics.

(* ================================================================= *)
(** ** Runtime Structure *)
(** http://webassembly.github.io/spec/core/exec/runtime.html *)


(* ----------------------------------------------------------------- *)
(** *** Values *)

(** Defined in [Values.v] *)


(* ----------------------------------------------------------------- *)
(** *** Results *)

(** In the current version of WebAssembly, a result can consist of at most one value. *)

Inductive result :=
  | R_val (_: list val)
  | R_trap. (* coincident with [trap] *)

(* We might need someway to coerce [admin_instr] to [result] *)


(* ----------------------------------------------------------------- *)
(** *** Addresses *)

Definition addr := nat.
Notation funcaddr := addr.
Notation tableaddr := addr.
Notation memaddr := addr.
Notation globaladdr := addr.


(* ----------------------------------------------------------------- *)
(** *** Module Instances *)

Record moduleinst :=
  {
    MI_types : list functype;
    MI_funcaddrs : list funcaddr;
    MI_tableaddrs : list tableaddr;
    (* memaddrs : list memaddr; *)
    (* globaladdrs : list globaladdr; *)
    (* exports : list exportinst; *)
  }.

Definition empty_moduleinst :=
  {|
    MI_types := [];
    MI_funcaddrs := [];
    MI_tableaddrs := [];
  |}.


(* ----------------------------------------------------------------- *)
(** *** Function Instances *)

(* Print Structure.func. *)

(* [func] is the AST func: 
     - type signature [F_type   : typeidx]
     - locals type    [F_locals : list valtype]
     - actual code    [F_body   : expr]  (expr := list instr)

   [funcinst] is the closure (heap-allocated, as all other "Xinst"):
     - environment   [FI_module : module_inst]
     - code pointer  [FI_code   : func]
     - type          [FI_type   : functype]

   [Frame] is the activation record (on stack): 
     - return arity  [A_arity  : nat]
     - actual locals [A_locals : list val]         (taken from stack)   (recorded in frame)
     - actual mdule  [A_module : moduleinst]       (taken from closure) (recorded in frame)
     - actual code   [code     : list admin_instr] (lifting from closure)
 *)

(* 
   I first modeled func inst as constructor and write own projections
   since Coq doesn't support ocaml-like inline record

    Inductive funcinst :=
      | Func (FI_type: functype) (FI_module: moduleinst) (FI_code: func)
      | Host (FI_type: functype) (FI_hostcode: hostfunc).

   But latern on I realized record + coercions would be more convenient.
 *)

Inductive hostfunc := .

Record funcinst__wasm :=
  {
    FI_type__wasm : functype;  (* spec overload [type] *)
    FI_module   : moduleinst;
    FI_code     : func;
  }.

Record funcinst__host :=
  {
    FI_type__host : functype;  (* spec overload [type] *)
    FI_hostcode : hostfunc;
  }.

Inductive funcinst :=
  | FI_wasm (_: funcinst__wasm)
  | FI_host (_: funcinst__host).

Coercion FI_wasm : funcinst__wasm >-> funcinst.
Coercion FI_host : funcinst__host >-> funcinst.

(* type is ad-hoc polymorphic *)

Definition FI_type (f: funcinst) : functype :=
  match f with
  | FI_wasm f => f.(FI_type__wasm)
  | FI_host f => f.(FI_type__host)
  end.

Notation " f '.(FI_type)' " := (FI_type f) (at level 50).


(* ----------------------------------------------------------------- *)
(** *** Table Instances *)

Notation funcelem := (option funcaddr).

Record tableinst :=
  {
    TI_elem : list funcelem;
    TI_max : option I32.t;  (* option u32 *)
  }.

Definition empty_tableinst :=
  {|
    TI_elem := [];
    TI_max := Some I32.zero;
  |}.

(* ----------------------------------------------------------------- *)
(** *** Memory Instances *)

Record meminst :=
  {
    MEI_data : list byte;
    MEI_max : option I32.t;  (* option u32 *)
  }.

(* ----------------------------------------------------------------- *)
(** *** Global Instances *)

(* ----------------------------------------------------------------- *)
(** *** Export Instances *)

(* ----------------------------------------------------------------- *)
(** *** External Values *)

(* ----------------------------------------------------------------- *)
(** *** Store *)
(** https://webassembly.github.io/multi-value/core/exec/runtime.html#store *)

Record store :=
  {
    S_funcs : list funcinst;
    S_tables : list tableinst;
    (* S_mems : list meminst; *)
    (* S_globals : list globalinst; *)
  }.

Definition empty_store :=
  {|
    S_funcs := [];
    S_tables := [];
  |}.


(* ----------------------------------------------------------------- *)
(** *** Stack *)

(** **** Activations and Frames *)

Record frame :=
  {
    A_locals: list val;
    A_module: moduleinst;
  }.

(** activation is coincident with the [Frame] admin_instr *)

Record activation :=
  {
    A_arity: nat;
    A_frame: frame;
  }.

Definition empty_frame :=
  {|
    A_locals := [];
    A_module := empty_moduleinst;
  |}.

Definition empty_activation :=
  {|
    A_arity := 0;
    A_frame := empty_frame;
  |}.

Definition upd_locals (F: frame) (x: nat) (v: val) :=
  match update_idx F.(A_locals) x v with
  | None => None
  | Some vs => Some
      {|
        A_locals := vs;
        A_module := F.(A_module);
      |}
  end.
  
Notation "F 'with_locals[' x ] = v" :=
  (upd_locals F x v)
  (at level 69, left associativity) : wasm_scope.


Lemma upd_locals_inv: forall F F' n c,
  (F with_locals[n] = c) = Some F' ->
  F'.(A_locals).[n] = Some c.
Proof.
  Abort.


(* test *)

Module FrameTests.

  Parameter c : val.
  Parameter c' : val.

  Example F0 := empty_frame.

  Example F0__none : F0.(A_locals).[0] = None.
  auto. Qed.

  Example F0__updatefail : (F0 with_locals[0] = c) = fail.
  auto. Qed.

  Example F1 :=
    {|
      A_locals := [c; c];
      A_module := empty_moduleinst;
    |}.

  Example F1__some : F1.(A_locals).[0] = Some c.
  auto. Qed.

  Example F1_upd_locals_inv: forall F',
    (F1 with_locals[0] = c') = Some F' ->
    F'.(A_locals).[0] = Some c'.
  Proof with eauto.
    unfold upd_locals.
    intros. simpl in *. 
    inversion H...
  Qed.

End FrameTests.


(** **** Expand *)

(** the original spec doesn't need to take acount of None case.
    since execution has assumed to pas the validaton
 *)

Definition expand (F: frame) (bt: blocktype) : option functype :=
  match bt with
  | BT_typeidx typeidx => F.(A_module).(MI_types).[typeidx]
  | BT_valtype opt_valtype => Some ([] --> (opt_to_rt opt_valtype))
  end.


(* ----------------------------------------------------------------- *)
(** *** Administrative Instructions *)

Inductive admin_instr :=
  | Plain (_: instr)
  | Trap
  | Invoke (closure: funcaddr)
  | Label (n: nat) (cont: list instr) (code: list admin_instr)
  | Frame (n: nat) (activation: frame) (code: list admin_instr).


(** lifting *)

Definition lift_plains (instrs: list instr) : list admin_instr :=
  map Plain instrs.

Definition lift_vals(vals: list val) : list instr :=
  map Const vals.

(* TBD: need a code to be able to lift to Frame *)
Definition lift_activation (a: activation) :=
  Frame a.(A_arity) a.(A_frame).


(** Coercions and Notations *)
(** since the coercion doesn't work well with [list X] so we introduce
    rather heavy notation for the lifting *)

Coercion Plain : instr >-> admin_instr.

Notation "↑ instrs" := (lift_plains instrs) (at level 60).         (* \uparrow *)
Notation "⇈ vals" := (lift_plains (lift_vals vals)) (at level 50). (* \upuparrows *)

Module AdminInstrCoercisonTest.

  (* The mechanism that introduce of Coercion is tricky.
     see [https://github.com/coq/coq/issues/10898]
   *)

  Parameter c : val.

  (* Unit tests on coerce one [instr] or [val] *)
  Example ai__one : admin_instr := Nop.
  Example av__one : admin_instr := c.

  (* Unit tests on coerce [instr] inside list *)
  Fail Example ai__fail : list admin_instr := [Nop].
  Program Example ai__program: list admin_instr := [Nop].
  Example ai__coerce: list admin_instr := [Nop : admin_instr].
  Example ai__notation : list admin_instr := ↑[Nop].

  (* Unit tests on coerce [val] inside list *)
  Example av__coerceinstr : list instr := [c: instr].
  Example av__coerceadmin : list admin_instr := [c: admin_instr].
  Example av__notation : list admin_instr := ⇈[c].

  (* [c] took two Coercion path: [val >-> instr >-> admin_instr] *)
  Example app__coerce: list admin_instr := [c: admin_instr] ++ [Nop: admin_instr].

  (* too complicated even for this [Program] to work *)
  Fail Program Example app__program := [c] ++ [Nop].

  (* could not coerce a [list X] directly. *)
  Example vs := [c].
  Fail Example app__coercelist := vs : list admin_instr.

  (* Notation is still the most elegant approach *)
  Example app__notation : list admin_instr := ⇈[c] ++ ↑[Nop].

  Example a : activation :=
    {|
      A_arity := 1;
      A_frame := empty_frame;
    |}.

End AdminInstrCoercisonTest.


(* ----------------------------------------------------------------- *)
(** *** Blocking Contexts *)
(** https://webassembly.github.io/multi-value/core/exec/runtime.html#block-contexts *)

(** blocking context is coincident with the [Label] admin_instr

    We found some inconsistency about the treatment on this:

    - reference interpreter :
      * having admin_instr [Breaking] and [Returning] that carried over all the unwinding vals until the [Label n] is reached and it will push the [n] val back.
      * the "jumping out" from all the blocking contexts is done step-by-step (one-by-one)

    - original paper and Isabelle all use a giganitic step to jump to the target label directly.
      * the problem is that during the Progress proof of type soundness we will need to build (show the exsistence)
        all the necessary decomposition of [instrs] anyway.

    - more problematically, in the spec
      * the formal notation is done in one "gigantic step",
      * the prose is demonstrated "step-by-step".

    - we will see which one to use
 *)


(* block contexts is defined as a type family indexed by the count of labels surronding a hole,
   i.e. dependent sum  *)

Inductive block_context : nat -> Type :=

  (* B0 ::= val∗ [_] instr∗  -- this is equiv to E_val *)
  | B_nil  : forall (vals: list val) (* [_] *) (instrs: list admin_instr),
               block_context 0

  (* Bk+1 ::= val∗ label n {instr∗} Bk end instr∗  *)
  | B_cons : forall {k: nat}
               (vals: list val)
               (n: nat) (cont: list instr)  (* Label *)
               (B: block_context k)
               (instrs: list admin_instr),
               block_context (k+1).

Fixpoint plug_block_context {k: nat} (B: block_context k) (hole: list admin_instr) : list admin_instr :=
  match B with
  | B_nil vals instrs => ⇈ vals ++ hole ++ instrs
  | B_cons vals n cont B' instrs =>
      ⇈ vals ++ [Label n cont (plug_block_context B' hole)] ++ instrs
  end.

Notation plug__B := plug_block_context.

Module BlockContextTest.

  Parameter c : val.

  Example vals := [c; c].
  Example instrs := ↑[Nop].
  Example cont := [Nop].

  Example B0 := B_nil vals instrs.
  (*
    it prints as if it's coerced

      Compute (plug__B B0 [Trap]).

      = [c; c; Trap; Nop]
        : list admin_instr

    But simply doing this would not type check.

      Example pB0 : (plug__B B0 [Trap]) = [c; c; Trap; Nop].

    [Program Example] provide extra Coercion hint:
  *)

  Program Example pB0 : (plug__B B0 [Trap]) = [c; c; Trap; Nop].
  auto. Qed.

  Example B1 := B_cons vals (*label*) 0 cont B0 (*end*) instrs.
  Program Example pB1 :
    (plug__B B1 [Trap]) = [c; c; Label 0 [Nop] [c; c; Trap; Nop]; Nop].
  Proof. auto. Qed.

End BlockContextTest.


(* ----------------------------------------------------------------- *)
(** *** Configurations *)

(** Notes on the configurations:

    (1) The spec defined configuration as store and an executing thread.
   
          Notation thread := (frame * (list admin_instr))%type.
          Notation config := (store * thread)%type.


    (2) However, the step relation is actually defined in terms of a 3-tuple.

          Notation config := (store * frame * (list admin_instr))%type.

        This make sense since instructions currently-defined are single-threaded,
        i.e., the machine always take a step in one thread.
       
        This has benefit that being closer to the spec sometimes.
        the spec use the notation of execution context implicitly use
        the _composed_ version and _decomposed_ version interchangbly.

        The cons are that to do proof on this, we will need to _figure out_
        the correct decomposition of execution context everytimes...
        although it should be rather straightforward since we could prove
        that any [list admin_instr] share the [unique decomposition] properties
        on the first occurence of [val].


    (3) Alternative is to be closer to OCaml ref interpeter.

          Notation code := (list val * list admin_instr)%type.
          Notation config := (store * frame * code)%type.

        This has the benefit to be closer to the original paper, ref interpeter,
        and some of the instructions that defined in the decomposed mannar.

        The main reason of doing so is that it made the step relation clear and
        proof potentially easier beacuse we explicit include this information.

    Potential future Work:
    One way to enrich our work is to prove the (2) and (3) are equivalent.
*)

Definition thread : Type := frame * list admin_instr.
Definition config : Type := store * thread.

Definition empty_thread : thread := (empty_frame, []).
Definition empty_config : config := (empty_store, empty_thread).

(* S; F; instrs *)
Notation S_F_instrs := (store * frame * list admin_instr)%type.

Definition config_to_tuple (cfg: config) : S_F_instrs :=
  match cfg with
  | (store, (F, instrs)) => (store, F, instrs)
  end.

(* Coercion config_to_tuple : config >-> S_F_instrs. *)
(* coercion is useless except confusing things during proof. *)

Notation "'$' cfg" := (config_to_tuple cfg) (at level 49).



(* ----------------------------------------------------------------- *)
(** *** Evaluation Contexts *)
(** https://webassembly.github.io/multi-value/core/exec/runtime.html#evaluation-contexts *)

(** There are at least 2 types of execution context:
    It's frank that Frame admin_instr is not a kind of EC.

        E ::= [_]
            | val⃰ E instr⃰
            | label_n {instr⃰} E end

    Technically, in the sense of "frame" in contextual semantics:

        Inductive frame : Type :=
          | F_stack : list val -> list admin_instr -> hole -> frame
          | F_label : N -> list admin_instr -> hole -> frame

    But they are somewhat overloading and could be coerce: 
    - val and instr are coincident.
    - Label EC and Label admin_instr are coincident.
    - EC has its own configuration... 
 *)

Inductive eval_context :=
  | E_hole 
  | E_seq (vals: list val) (E: eval_context) (instrs: list admin_instr)
  | E_label (n: nat) (cont: list instr) (E: eval_context).

Fixpoint plug_eval_context (E: eval_context) (hole: list admin_instr) : list admin_instr :=
  match E with
   | E_hole => hole
   | E_seq vals E instrs => ⇈vals ++ (plug_eval_context E hole) ++ instrs
   | E_label n cont E => [Label n cont (plug_eval_context E hole)]
  end.

Notation plug__E := plug_eval_context.


Module EvalContextTest.

  Parameter c : val.

  Example vals := [c; c].
  Example instrs := ↑[Nop].
  Example cont := [Nop].

  Example E0 := E_hole.
  Example E1 := E_seq vals E0 instrs.
  Example E2 := E_label 0 cont E1. 

  Example e0 : (plug__E E0 [Trap]) = [Trap].
  auto. Qed.

  Program Example e1 : (plug__E E1 [Trap]) = [c; c; Trap; Nop].
  auto. Qed.

  Program Example e2 : (plug__E E2 [Trap]) =  [Label 0 [Nop] [c; c; Trap; Nop]].
  auto. Qed.

End EvalContextTest.


(* ================================================================= *)
(** ** Instructions *)
(** https://webassembly.github.io/multi-value/core/exec/instructions.html#instructions *)


(* Failure on [val_of] is a _runtime type error_ (getting stuck).
   Returning [Trap] is an acceptable result for proving soundness. 

   The reference interepter implicit exploit the property where 
   there is a 1-1 correspondence between:

        val := @op   I32.t       I64.t    ...
                      ↓           ↓
        ops := @op  IOp32.op   IOp64.op   ...

   So we can safely do the [val_of]


   here we have two approaches to exploit and prove this:

   (1) We have some predicates making this requirements explicit.

      Inductive rep_of_val {i32 i64 f32 f64 : Type} :
          forall (ops : @op i32 i64 f32 f64), val -> rep_type_of ops -> Prop :=
        | RV_i32 : forall i, rep_of_val (i32 _) (i32 i) i
        | ...
        .

      Inductive step_simple : list admin_instr -> list admin_instr -> Prop :=
        | SS_binop__some : forall op c1 v1 c2 v2 c v,
            rep_of_val op c1 v1 ->
            rep_of_val op c2 v2 ->
            eval_binop op v1 v2 = Some v ->
            rep_of_val op c v ->
            ↑[Const c1; Const c2; Binop op] ↪s ↑[Const c]

    (2) making these two failures distinct.
        e.g. here we add a new sum type [runtime_err] besides [option]

        and we then prove [Err] case doesn't exist after validation. 
 *)


(* TODO: In terms of name, we might want to merge [SS] and [SC] into one? *)

Reserved Notation "instrs1 '↪s' instrs2" (at level 70).
Inductive step_simple : list admin_instr -> list admin_instr -> Prop :=

(* ----------------------------------------------------------------- *)
(** *** Numeric Instruction *)

(* technically, the [c] here are typed [tc : val] *)

  | SS_unop__some : forall op c1 c,
      eval_unop op c1 = Ok (Some c) ->
      ↑[Const c1; Unop op] ↪s ↑[Const c]

  | SS_unop__none : forall op c1,
      eval_unop op c1 = Ok None ->
      ↑[Const c1; Unop op] ↪s [Trap]

  | SS_binop__some : forall op c1 c2 c,
      eval_binop op c1 c2 = Ok (Some c) ->
      ↑[Const c1; Const c2; Binop op] ↪s ↑[Const c]

  | SS_binop__none : forall op c1 c2, 
      eval_binop op c1 c2 = Ok None ->
      ↑[Const c1; Const c2; Binop op] ↪s [Trap]

  | SS_testop: forall op c1 (c: bool),
      eval_testop op c1 = Ok c ->
      ↑[Const c1; Testop op] ↪s ↑[Const c]

  | SS_relop: forall op c1 c2 c,
      eval_relop op c1 c2 = Ok c ->
      ↑[Const c1; Const c2; Relop op] ↪s ↑[Const c]

(* ----------------------------------------------------------------- *)
(** *** Parametric Instruction *)

  | SS_drop : forall (val: val),
      let val : instr := val in
      ↑[val; Drop] ↪s []

  (* A exprimental alternative definition using per item Coercion *)
  | SS_select1 : forall (val1 val2 : val) c,
      let val1 : instr := val1 in
      let val2 : instr := val2 in
      c <> I32.zero ->
      ↑[val1; val2; Const (i32 c); Select] ↪s ↑[val1]

  | SS_select2 : forall (val1 val2 : val) c,
      let val1 : instr := val1 in
      let val2 : instr := val2 in
      c = I32.zero ->
      ↑[val1; val2; Const (i32 c); Select] ↪s ↑[val2]

  (* | SS_select1 : forall c1 c2 c, *)
  (*     c <> I32.zero -> *)
  (*     ↑[Const c1; Const c2; Const (i32 c); Select] ↪s ↑[Const c1] *)

  (* | SS_select2 : forall c1 c2 c, *)
  (*     c = I32.zero -> *)
  (*     ↑[Const c1; Const c2; Const (i32 c); Select] ↪s ↑[Const c2] *)

(* ----------------------------------------------------------------- *)
(** *** Control Instruction *)

  | SS_nop : 
      ↑[Nop] ↪s []

  | SS_unreachable : 
      ↑[Unreachable] ↪s [Trap]

  | SS_br : forall n instrs l (Bl: block_context l) vals,
      length vals = n ->
      [Label n instrs (plug__B Bl (⇈vals ++ ↑[Br l]))] ↪s ⇈vals ++ ↑instrs

  | SS_br_if1 : forall c l,
      c <> I32.zero ->
      ↑[Const (i32 c); Br_if l]  ↪s ↑[Br l]

  | SS_br_if2 : forall c l,
      c = I32.zero ->
      ↑[Const (i32 c); Br_if l]  ↪s []

  | SS_br_table__i : forall ls l__N l__i (i: nat),
      ls.[i] = Some l__i ->
      ↑[Const (i32 (i : I32.t)); Br_table ls l__N]  ↪s  ↑[Br l__i]

  | SS_br_table__N : forall ls l__N (i: nat),
      length ls <= i ->
      ↑[Const (i32 (i : I32.t)); Br_table ls l__N]  ↪s  ↑[Br l__N]

(* ----------------------------------------------------------------- *)
(** *** Control Instruction - Function Call Related *)

  | SS_return : forall n F k (Bk : block_context k) vals,
      length vals = n ->
      [Frame n F (plug__B Bk (⇈vals ++ ↑[Return]))] ↪s ⇈vals

(* ----------------------------------------------------------------- *)
(** *** Block *)

  | SS_block__exit : forall n m vals instrs,
      length vals = m ->
      [Label n instrs (⇈vals)]  ↪s ⇈vals

(* ----------------------------------------------------------------- *)
(** *** Function Calls *)
(** **** Returning from a function *)

  | SS_frame__exit : forall n F vals,
      length vals = n ->
      [Frame n F (⇈vals)]  ↪s ⇈vals

where "instrs1 '↪s' instrs2"  := (step_simple instrs1 instrs2).


(* S; F; instr* ↪ S'; F'; instr'* *)

Reserved Notation "SFI1 '↪' SFI2" (at level 69).
Inductive step: S_F_instrs -> S_F_instrs -> Prop :=

(* ----------------------------------------------------------------- *)
(** *** Lifting ↪s *)
(** simple (no S or F involved) and plain (non-admin) are different:
    - admin instrs always take a non-simple step.
    - plain instrs might take a non-simple step as well.
 *)

  | SC_simple : forall S F instrs instrs',
      instrs ↪s instrs' ->
      (S, F, instrs) ↪ (S, F, instrs')

(* ----------------------------------------------------------------- *)
(** *** Memory Instruction *)

  | SC_local_get : forall S F x v, 
      F.(A_locals).[x] = Some v ->
      (S, F, ↑[Local_get x]) ↪ (S, F, ↑[Const v])

  | SC_local_set : forall S F F' x v, 
      Some F' = F with_locals[x] = v ->
      (S, F, ↑[Const v; Local_set x]) ↪ (S, F', [])

  | SC_local_tee : forall S F x v, 
      (S, F, ↑[Const v; Local_tee x]) ↪ (S, F, ↑[Const v; Const v; Local_set x])

  (* | SC_global_get *)
  (* | SC_global_set *)

(* ----------------------------------------------------------------- *)
(** *** Control Instruction *)

  (* 这里应该根据 BT 的 n -> m 带 n 个 var 进 Label 里来, 然后标记 label 为 m
     原 paper 更为正确

     Interpreter 的做法也是正确的....还更新了前面的 val 部分

        let args, vs' = take n1 vs e.at, drop n1 vs e.at in
        vs', [Label (n2, [], (args, List.map plain es')) @@ e.at]

     In terms of preservation/progress proof, I think we can always extract
     sufficient number of vals from the well-type premise. 
   *)
                                      
  | SC_block : forall S F m n ts1 ts2 bt instrs vs,
      m = length ts1 ->
      n = length ts2 ->
      length vs = m ->
      expand F bt = Some (ts1 --> ts2) ->
      (S, F, vs ++ ↑[Block bt instrs]) ↪ (S, F, [Label n ϵ (vs ++ ↑instrs)])

  | SC_loop : forall S F m n ts1 ts2 bt instrs vs,
      m = length ts1 ->
      n = length ts2 ->
      length vs = m ->
      expand F bt = Some (ts1 --> ts2) ->
      (S, F, vs ++ ↑[Loop bt instrs]) ↪ (S, F, [Label n [Loop bt instrs] (vs ++ ↑instrs)])

  (* The original paper definition (and Isabelle) simply desugar [if] into [block]
     But here we faithfully represent the spec and made the rule explicit. *)

  | SC_if1 : forall S F m n ts1 ts2 bt instrs1 instrs2 c vs,
      m = length ts1 ->
      n = length ts2 ->
      length vs = m ->
      c <> I32.zero ->
      expand F bt = Some (ts1 --> ts2) ->
      (S, F, vs ++ ↑[Const (i32 c); If bt instrs1 instrs2]) ↪ (S, F, [Label n ϵ (vs ++ ↑instrs1)])

  | SC_if2 : forall S F m n ts1 ts2 bt instrs1 instrs2 c vs,
      m = length ts1 ->
      n = length ts2 ->
      length vs = m ->
      c = I32.zero ->
      expand F bt = Some (ts1 --> ts2) ->
      (S, F, vs ++ ↑[Const (i32 c); If bt instrs1 instrs2]) ↪ (S, F, [Label n ϵ (vs ++ ↑instrs2)])

(* ----------------------------------------------------------------- *)
(** *** Control Instruction - Function Call Related *)

  | SC_call : forall S F x a,
      F.(A_module).(MI_funcaddrs).[x] = Some a ->
      (S, F, ↑[Call x]) ↪ (S, F, [Invoke a])

  | SC_call_indirect : forall S F (i: nat) x a (ta: tableaddr) (tab: tableinst) f ft,

      (* S.tables[F.module.tableaddrs[0]].elem[i] = a *)

      F.(A_module).(MI_tableaddrs).[0] = Some ta ->
      S.(S_tables).[ta] = Some tab ->
      tab.(TI_elem).[i] = Some (Some a) ->

      S.(S_funcs).[a] = Some f ->

      (* F.module.types[x] = f.type *)

      F.(A_module).(MI_types).[x] = Some ft ->

      (* this [FI_type] is polymorphic over wasm and host *)
      f.(FI_type) = ft ->

      (* Coercion [nat_to_i32] happened to [i] here. *)
      (S, F, ↑[Const (i32 (i: I32.t)); Call_indirect x]) ↪ (S, F, [Invoke a])

  | SS_call_indirect__trap : forall S F i x,
      (S, F, ↑[Const (i32 i); Call_indirect x]) ↪ (S, F, [Trap])

(* ----------------------------------------------------------------- *)
(** *** Function Call *)

  | SC_invoke : forall S F' F vals a n m ts1 ts2 instrs f x ts,

      S.(S_funcs).[a] = Some (FI_wasm f) ->

      length ts1 = n ->
      length ts2 = m ->
      f.(FI_type) = ts1 --> ts2 ->

      f.(FI_code) = {| F_type := x; F_locals := ts; F_body := instrs |} ->

      F = {| A_module := f.(FI_module); A_locals := vals ++ (zeros ts) |} ->

(*     S;      val^n   (invoke a)  ↪  S;      frame_m{F} label_m {}   instr* end end *)
      (S, F', ⇈vals ++ [Invoke a]) ↪ (S, F', [Frame m F [Label m [] (↑instrs)]])

(** **** Host Functions *)

  (* | SC_invoke_host  *)
  (* | SC_invoke_host__trap  *)

(* ----------------------------------------------------------------- *)
(** *** Evaluation Contexts *)

(*
       S; F;   instr*  ↪ S′; F′;   instr′*
    ------------------------------------------
       S; F; E[instr*] ↪ S′; F′; E[instr′*]
*)

  | SC_E : forall E S S' F F' instrs instrs',
      (S, F,         instrs) ↪ (S', F',         instrs') ->
      (S, F, plug__E E instrs) ↪ (S', F', plug__E E instrs')

(*
       S;              F'; instr*     ↪ S';             F''; instr′*
    ----------------------------------------------------------------------
       S; F;  frame_n {F'} instr* end ↪ S'; F; frame_n {F''} instr'* end
*)

  | SC_frame : forall S S' F F' F'' n instrs instrs',
      (S,             F',instrs ) ↪ (S',             F'',instrs' ) ->
      (S, F, [Frame n F' instrs]) ↪ (S', F, [Frame n F'' instrs'])

(** **** Trap *)

  | SC_trap__E : forall E S F, 
      (S, F, plug__E E [Trap]) ↪ (S, F, [Trap])

  | SC_trap__frame : forall S F n F', 
      (S, F, [Frame n F' [Trap]]) ↪ (S, F, [Trap])
                             
(* ----------------------------------------------------------------- *)
(** *** Expressions *)
(** https://webassembly.github.io/multi-value/core/exec/instructions.html#expressions *)
(* since

      Definition/Notation expr := list instr

   I am afraid that I have implicitly include this rule all over the place
   that we define the structure with expr...

   Do we really need this?
*)

  | SC_expr : forall S S' F F' (e: expr) (e': expr) instrs instrs', 
    e  = instrs ->
    e' = instrs' ->
    (S, F, ↑e) ↪ (S', F', ↑e') ->
    (S, F, ↑instrs) ↪ (S', F', ↑instrs') 

where "SFI1 '↪' SFI2" := (step SFI1 SFI2).

Module ConfigStepTest.

  Example e : forall (S S': store) (T T': thread),
    config_to_tuple (S, T) ↪ config_to_tuple (S', T').
  Abort. 

  Example e2 : forall (S S': store) (T T': thread),
    ($(S, T)) ↪ ($(S', T')).
  Abort. 

  Example e3 : forall (S S': store) (T T': thread),
    $(S, T) ↪ $(S', T') ->
    $(S, T) ↪ $(S', T').
  Abort. 

End ConfigStepTest.


(* ================================================================= *)
(** ** Archive (Deprecated) *)

(* Originally, I defined Eval Context as a "pre-filled" things.

      Inductive eval_context :=
        | E_val (vals: list val) (hole: list admin_instr) (instrs: list admin_instr)
        | E_label (n: nat) (cont: list instr) (hole: list admin_instr).

   and represent the transition inside a eval context, i.e.

      S; F; E[instr*] ↪ S′; F′; E[instr′*]

   as a step relation on a special version of config via eval context:

      Notation E_config := (store * frame * eval_context)%type.

      Reserved Notation "E_cfg1 '↪' E_cfg2" (at level 40).
      Inductive step : E_config -> E_config -> Prop :=

        | SC_val : forall S S' F F' vs es instrs instrs',
            (S, F, instrs) ↪c (S', F', instrs') ->
            (S, F, (E_val vs instrs es)) ↪ (S', F', (E_val vs instrs' es))

        | SC_label : forall S S' F F' n vs es instrs instrs',
            (S, F, instrs) ↪c (S', F', instrs') ->
            (S, F, (E_label n es instrs)) ↪ (S', F', (E_label n es instrs'))

      where "E_cfg1 '↪' E_cfg2" := (step E_cfg1 E_cfg2).

*)





                                          
