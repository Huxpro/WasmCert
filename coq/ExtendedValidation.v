(* ***************************************************************** *)
(* ExtendedValidation.v                                              *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)

(* ################################################################# *)
(** * Extended Validation *)
(** In order to state and prove soundness precisely, the typing rules
    must be extended to the dynamic components of the abstract runtime,
    that is, the store, configurations, and administrative instructions
 *)

From Wasm Require Import Validation.
From Wasm Require Import Execution.

  
(**************************************************************)
(** ** Implicit Types - Source of Truth *)
(** https://coq.inria.fr/refman/language/gallina-extensions.html#implicit-types-of-variables

    - help with strictly check our naming convention.
    - it works up to prime (b') and number postfix (val1).
    - can be explicitly override when needed.
    - it's not shared so have to be copied.
*)

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
(** ** Values and Results *)

Reserved Notation " '⊢v' v ∈ t" (at level 70).
Inductive valid_value : val -> valtype -> Prop :=

  | VV : forall val t,
      t = type_of val ->
      ⊢v val ∈ t

where " '⊢v' v ∈ t" := (valid_value v t).
Hint Constructors valid_value.


(** This is not explicitly defined but occured as

      (⊢ val : t)*
*)
Reserved Notation "'⊢v*' vals ∈ ts" (at level 70).
Inductive valid_values : list val -> list valtype -> Prop :=

  | VVS : forall vals ts,
      Forall2 (fun val t => ⊢v val ∈ t) vals ts ->
      ⊢v* vals ∈ ts

where " '⊢v*' vals ∈ ts" := (valid_values vals ts).
Hint Constructors valid_values.


Reserved Notation " '⊢r' r ∈ ts" (at level 70).
Inductive valid_result : result -> list valtype -> Prop :=

  | VR_val : forall vals ts,
      Forall2 (fun val t => ⊢v val ∈ t) vals ts ->
      ⊢r R_val vals ∈ ts

  | VR_trap : forall ts,
      ⊢r R_trap ∈ ts

where " '⊢r' r ∈ ts" := (valid_result r ts).


(* ================================================================= *)
(** ** Alternative Def of Val as Proof-Carry Instr *)

(*
Reserved Notation " 'isval' v " (at level 70).
Inductive is_val : instr -> Prop :=

  | Val : forall c,
      isval (Const c)

where " 'isval' v " := (is_val v).

Record value :=
  {
    v : instr;
    H : isval v;
  }. 

Example v1 :=
  {|
    v := Const (i32 I32.zero);
    H := Val (i32 I32.zero);
  |}.

Compute v1.(H).

(* pattern match as dependent pair will give you this information *)

Fail Definition get_c (i: value) : val :=
  match (i.(v), i.(H)) with
    | (Const c, Val _) => c
  end.
*)

(* ================================================================= *)
(** ** Store Validity *)

(* ----------------------------------------------------------------- *)
(** *** Memory Instances *)

(* ----------------------------------------------------------------- *)
(** *** Global Instances *)

(* ----------------------------------------------------------------- *)
(** *** Export Instances *)

(* ----------------------------------------------------------------- *)
(** *** Module Instances *)

Reserved Notation "S '⊢mi' Mi '∈' C" (at level 70).
Inductive valid_moduleinst : store -> moduleinst -> context -> Prop :=

  | VMI: forall S C fts fts' tts fas tas,
      ⊢ft* fts ok ->

      (* external instances check * 4 instantiated as func/table/mem/global *)

      (* since other field of [C] doesn't matter... *)
      C.(C_types) = fts  ->
      C.(C_funcs) = fts' ->
      C.(C_tables) = tts ->

      S ⊢mi {|
              MI_types := fts;
              MI_funcaddrs := fas;
              MI_tableaddrs := tas;
            |} ∈ C

where "S '⊢mi' Mi '∈' C"  := (valid_moduleinst S Mi C).

(* ----------------------------------------------------------------- *)
(** *** Function Instances *)

Reserved Notation "S '⊢fi' fi '∈' ft" (at level 70).
Inductive valid_funcinst : store -> funcinst -> functype -> Prop :=

  | VFI: forall S C ft mi f,
        ⊢ft ft ok ->
      S ⊢mi mi ∈ C ->
      C ⊢f f ∈ ft ->
      S ⊢fi {| FI_type__wasm := ft; FI_module := mi; FI_code := f |} ∈ ft

where "S '⊢fi' fi '∈' ft"  := (valid_funcinst S fi ft).
Hint Constructors valid_funcinst.


(** This is not explicitly defined but occured as

      (⊢ funcinst : functype)*
*)
Reserved Notation "S '⊢fi*' fis ∈ fts" (at level 70).
Inductive valid_funcinsts : store -> list funcinst -> list functype -> Prop :=

  | VFIS: forall S fis fts,
      Forall2 (fun funcinst functype => S ⊢fi funcinst ∈ functype) fis fts ->  
      S ⊢fi* fis ∈ fts

where "S '⊢fi*' fis ∈ fts" := (valid_funcinsts S fis fts).
Hint Constructors valid_funcinsts.


(* ----------------------------------------------------------------- *)
(** *** Host Function Instances *)

(* ----------------------------------------------------------------- *)
(** *** Table Instances *)

Reserved Notation "S '⊢ti' ti '∈' tt" (at level 70).
Inductive valid_tableinst : store -> tableinst -> tabletype -> Prop :=

  | VTI: forall S (fes : list (option funcaddr)) n m__opt, 

      length fes = n ->

      (* valid external? fa n times *)

      ⊢tt ({| L_min := n; L_max := m__opt |}, funcref) ok ->

      S ⊢ti {|
          TI_elem := fes;
          TI_max  := m__opt;
        |} ∈ ({| L_min := n; L_max := m__opt |}, funcref)

where "S '⊢ti' ti '∈' tt"  := (valid_tableinst S ti tt).
Hint Constructors valid_tableinst.


(** This is not explicitly defined but occured as

      (⊢ tableinst : tabletype)*
*)
Reserved Notation "S '⊢ti*' tis ∈ tts" (at level 70).
Inductive valid_tableinsts : store -> list tableinst -> list tabletype -> Prop :=

  | VTIS: forall S tis tts,
      Forall2 (fun tableinst tabletype => S ⊢ti tableinst ∈ tabletype) tis tts ->  
      S ⊢ti* tis ∈ tts

where "S '⊢ti*' tis ∈ tts" := (valid_tableinsts S tis tts).
Hint Constructors valid_tableinsts.


(* ----------------------------------------------------------------- *)
(** *** Store *)

Reserved Notation "'⊢S' S 'ok'" (at level 70).
Inductive valid_store : store -> Prop :=

  | VS: forall S funcinsts tableinsts functypes tabletypes,

      (* why not just ok? *)
      S ⊢fi* funcinsts ∈ functypes ->
      S ⊢ti* tableinsts ∈ tabletypes ->

      S = {|
        S_funcs := funcinsts;
        S_tables := tableinsts;
      |} ->
      ⊢S S ok

where "'⊢S' S 'ok' " := (valid_store S).
Hint Constructors valid_store.



(* ================================================================= *)
(** ** Configuration Validity *)

(** Mutualy Recursive Definition - Pre-defined Notation  *)

Reserved Notation "S '⊢A' F '∈' C " (at level 70).
Reserved Notation "S_ret '⊢T' T '∈' ret " (at level 70).
Reserved Notation "'⊢c' cfg '∈' rt " (at level 70).
Reserved Notation "S_C '⊢a' ainstr '∈' ft " (at level 70).
Reserved Notation "S_C '⊢a*' ainstrs '∈' ft" (at level 70).

(* ----------------------------------------------------------------- *)
(** *** Configuration *)

Inductive valid_config : config -> resulttype -> Prop :=

  | VC: forall S T rt,
      ⊢S S ok ->
      (S, None) ⊢T T ∈ rt ->
      ⊢c (S, T) ∈ rt

(* ----------------------------------------------------------------- *)
(** *** Threads *)

with valid_thread : (store * option resulttype) -> thread -> resulttype -> Prop :=

  | VT: forall S F C (rt__opt : option resulttype) rt ainstrs, 
      S ⊢A F ∈ C ->
      (S, C with_return = rt__opt) ⊢a* ainstrs ∈ [] --> rt ->
      (S, rt__opt) ⊢T (F, ainstrs) ∈ rt

(* ----------------------------------------------------------------- *)
(** *** Frames *)
(** Since name [f] is used by [func] and [a] for [admin_instr]
    we use [A]ctivation for Frame (same as spec Latex)
 *)

with valid_frame : store -> frame -> context -> Prop :=

  | VA: forall S C vals mi ts,
      S ⊢mi mi ∈ C ->
      ⊢v* vals ∈ ts ->
      S ⊢A {| A_locals := vals; A_module := mi |} ∈ (C with_locals = ts)

(** The spec simply prepend a [ts]:

      S ⊢f {| A_locals := vals; A_module := mi |} ∈ (C,locals ts)

    Recall issue https://github.com/WebAssembly/spec/pull/1077
    we are assuming the [C.locals = ϵ] because of no nested fun.
  *)

(* ================================================================= *)
(** ** Administrative Instructions *)

with valid_admin_instr : (store * context) -> admin_instr -> functype -> Prop :=

  | VAI_instr : forall S C (instr: instr) ft,
      C ⊢ instr ∈ ft ->
      (S,C) ⊢a (instr: admin_instr) ∈ ft

  | VAI_trap : forall S C ts1 ts2,
      (S,C) ⊢a Trap ∈ ts1 --> ts2

  | VAI_invoke : forall S C fa ts1 ts2,
      (* TODO: external check
         (assume internal always success?) *)
      (S,C) ⊢a Invoke fa ∈ ts1 --> ts2

  (* | VAI_init_elem *)
  (* | VAI_init_data *)

  | VAI_label : forall S C n instrs0 ainstrs ts1 ts2,
      (* https://github.com/WebAssembly/multi-value/pull/35 *)
      length ts1 = n ->
      (S,C) ⊢a* ↑instrs0 ∈ ts1 --> ts2 ->
      (S,(C,labels ts1)) ⊢a* ainstrs ∈ [] --> ts2 ->
      (S,C) ⊢a Label n instrs0 ainstrs ∈ [] --> ts2

  | VAI_frame : forall S C ainstrs ts n F,
      length ts = n ->
      (S, Some ts) ⊢T (F, ainstrs) ∈ ts ->
      (S,C) ⊢a Frame n F ainstrs ∈ [] --> ts


with valid_admin_instrs : store * context -> list admin_instr -> functype -> Prop :=

  | VAIS: forall S C (instrs : list instr) ft,
      C ⊢* instrs ∈ ft ->
      (S,C) ⊢a* ↑instrs ∈ ft


where "S_C '⊢a' ainstr '∈' ft " := (valid_admin_instr S_C ainstr ft)
  and "S_C '⊢a*' ainstrs '∈' ft" := (valid_admin_instrs S_C ainstrs ft)
  and "S '⊢A' F '∈' C " := (valid_frame S F C)
  and "S_ret '⊢T' T '∈' ret " := (valid_thread S_ret T ret)
  and "'⊢c' cfg '∈' rt " := (valid_config cfg rt).


Hint Constructors valid_admin_instr.
Hint Constructors valid_admin_instrs.
Hint Constructors valid_frame.
Hint Constructors valid_thread.
Hint Constructors valid_config.



(* ================================================================= *)
(** ** Store Extension (Weakening) *)

(* ----------------------------------------------------------------- *)
(** *** Function Instance *)

Reserved Notation "⊢fi fi1 '⪯' fi2 " (at level 70).
Inductive extend_funcinst : funcinst -> funcinst -> Prop :=

  | EFI: forall fi,
      ⊢fi fi ⪯ fi  (* refl *)

where "⊢fi fi1 '⪯' fi2 "  := (extend_funcinst fi1 fi2).
Hint Constructors extend_funcinst.
         
(** This is not explicitly defined but occured as

      (funcinst1 : funcinst1')*
*)
Reserved Notation "⊢fi* fis1 '⪯' fis2 " (at level 70).
Inductive extend_funcinsts : list funcinst -> list funcinst -> Prop :=

  | EFIS: forall fis fis',
      Forall2 (fun fi fi' => ⊢fi fi ⪯ fi') fis fis' ->  
      ⊢fi* fis ⪯ fis'

where "⊢fi* fis1 '⪯' fis2 " := (extend_funcinsts fis1 fis2).
Hint Constructors valid_funcinsts.


(* ----------------------------------------------------------------- *)
(** *** Table Instance *)

Reserved Notation "⊢ti ti1 '⪯' ti2 " (at level 70).
Inductive extend_tableinst : tableinst -> tableinst -> Prop :=

  | ETI: forall es1 es2 n1 n2 m__opt,
      length es1 = n1 ->
      length es2 = n2 ->
      n1 <= n2 ->
      ⊢ti {| TI_elem := es1; TI_max := m__opt |}
        ⪯ {| TI_elem := es2; TI_max := m__opt |}

where "⊢ti ti1 '⪯' ti2 " := (extend_tableinst ti1 ti2).
Hint Constructors extend_tableinst.

(** This is not explicitly defined but occured as

      (tableinst1 : tableinst1')*
*)
Reserved Notation "⊢ti* tis1 '⪯' tis2 " (at level 70).
Inductive extend_tableinsts : list tableinst -> list tableinst -> Prop :=

  | ETIS: forall tis tis',
      Forall2 (fun ti ti' => ⊢ti ti ⪯ ti') tis tis' ->  
      ⊢ti* tis ⪯ tis'

where "⊢ti* tis1 '⪯' tis2 " := (extend_tableinsts tis1 tis2).
Hint Constructors extend_tableinst.

(* ----------------------------------------------------------------- *)
(** *** Memory Instance *)

(* ----------------------------------------------------------------- *)
(** *** Global Instance *)

(* ----------------------------------------------------------------- *)
(** *** Store *)

Reserved Notation "⊢S S1 '⪯' S2 " (at level 70).
Inductive extend_store : store -> store -> Prop :=

  | ES: forall S1 S2
        funcinsts1 funcinsts1' funcinsts2
        tableinsts1 tableinsts1' tableinsts2,

      S1.(S_funcs) = funcinsts1 ->
      S2.(S_funcs) = funcinsts1' ++ funcinsts2 ->
      ⊢fi* funcinsts1 ⪯ funcinsts1' ->

      S1.(S_tables) = tableinsts1 ->
      S2.(S_tables) = tableinsts1' ++ tableinsts2 ->
      ⊢ti* tableinsts1 ⪯ tableinsts1' ->

      ⊢S S1 ⪯ S2

where "⊢S S1 '⪯' S2" := (extend_store S1 S2).
Hint Constructors extend_store.