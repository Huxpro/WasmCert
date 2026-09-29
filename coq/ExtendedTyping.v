(* ***************************************************************** *)
(* ExtendedTyping.v                                                  *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)

(* ################################################################# *)
(** * Extended Typing *)
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
(** ** External Typing  "Execuction - Module" *)
(* https://webassembly.github.io/multi-value/core/exec/modules.html *)

(* It's different with "Validation - Types - External Types"
   in that these are auxilary typing in runtime, typed against store.
 *)

Reserved Notation "S '⊢ev' ev '∈' et" (at level 70).
Inductive valid_externval : store -> externval -> externtype -> Prop :=

  | VEV_func: forall S a ft,
      (exists fi,
          S.(S_funcs).[a] = Some fi /\
          fi.(FI_type) = ft
      ) ->
      S ⊢ev EV_func a ∈ ET_func ft
      
  | VEV_table: forall S a (fes : list funcelem) n m__opt,
      length fes = n ->
      S.(S_tables).[a] = Some {| TI_elem := fes; TI_max  := m__opt; |} ->
      S ⊢ev EV_table a ∈ ET_table ({| L_min := n; L_max := m__opt |}, funcref)

  (* | VEV_mem: forall S a m__opt bs, *)
  (*     (exists n, length bs = n * 65536) ->  (* 64 Ki *) *)
  (*     S.(S_mems).[a] = Some {| MEI_data := bs; MEI_max  := m__opt; |} -> *)
  (*     S ⊢ev EV_mem a ∈ ET_mem {| L_min := n; L_max := m__opt |} *)

  (* | VEV_global: forall S a mut t, *)
  (*     S.(S_globals).[a] = Some {| GI_value := val; GI_mut  := mut; |} -> *)
  (*     S ⊢ev EV_global a ∈ ET_global (mut, t) *)

where "S '⊢ev' ev '∈' et"  := (valid_externval S ev et).
Hint Constructors valid_externval.


(** This is not explicitly defined but occured as

      (S ⊢ func a : func functype)*
*)
Reserved Notation "S '⊢fa*' fas '∈' fts" (at level 70).
Inductive valid_funcaddrs : store -> list funcaddr -> list functype -> Prop :=

  | VFAS: forall S fas fts,
      Forall2 (fun fa ft => S ⊢ev EV_func fa ∈ ET_func ft) fas fts ->
      S ⊢fa* fas ∈ fts
      
where "S '⊢fa*' fas '∈' fts"  := (valid_funcaddrs S fas fts).
Hint Constructors valid_funcaddrs.


(** This is not explicitly defined but occured as

      ((S ⊢ func fa : func functype)^?)^n

    we definied in terms of [fe] since [funcelem = option funcaddr] 
*)
Reserved Notation "S '⊢fe*' fes '∈' fts" (at level 70).
Inductive valid_funcelems : store -> list funcelem -> list functype -> Prop :=

  | VFES: forall S fes fts,
      Forall2 (fun fe ft =>
                 match fe with
                 | Some fa => S ⊢ev EV_func fa ∈ ET_func ft
                 | None => True
                 end
              ) fes fts ->
      S ⊢fe* fes ∈ fts
      
where "S '⊢fe*' fes '∈' fts"  := (valid_funcelems S fes fts).
Hint Constructors valid_funcelems.


(** This is not explicitly defined but occured as

      (S ⊢ table a : table tabletype)*
*)
Reserved Notation "S '⊢ta*' tas '∈' tts" (at level 70).
Inductive valid_tableaddrs : store -> list tableaddr -> list tabletype -> Prop :=

  | VTAS: forall S tas tts,
      Forall2 (fun ta tt => S ⊢ev EV_table ta ∈ ET_table tt) tas tts ->
      S ⊢ta* tas ∈ tts
      
where "S '⊢ta*' tas '∈' tts"  := (valid_tableaddrs S tas tts).
Hint Constructors valid_tableaddrs.


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


Reserved Notation " '⊢r' res ∈ rt" (at level 70).
Inductive valid_result : result -> list valtype -> Prop :=

  | VR_vals : forall vals rt,
      Forall2 (fun val t => ⊢v val ∈ t) vals rt ->
      ⊢r R_vals vals ∈ rt

  | VR_trap : forall rt,
      ⊢r R_trap ∈ rt

where " '⊢r' res ∈ rt" := (valid_result res rt).
Hint Constructors valid_result.


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

Reserved Notation "  '⊢S' S 'ok'" (at level 70).
Reserved Notation "S '⊢fi' fi '∈' ft" (at level 70).
Reserved Notation "S '⊢fi*' fis ∈ fts" (at level 70).
Reserved Notation "S '⊢ti' ti '∈' tt" (at level 70).
Reserved Notation "S '⊢ti*' tis ∈ tts" (at level 70).
Reserved Notation "S '⊢mei' mei '∈' met" (at level 70).
Reserved Notation "S '⊢gi' gi '∈' gt" (at level 70).
Reserved Notation "S '⊢exi' exi 'ok'" (at level 70).
Reserved Notation "S '⊢mi' Mi '∈' C" (at level 70).

(* ----------------------------------------------------------------- *)
(** *** Store *)

Inductive valid_store : store -> Prop :=

  | VS: forall S funcinsts tableinsts,

      (* why not just ok? *)
      (exists functypes,  S ⊢fi* funcinsts ∈ functypes) ->
      (exists tabletypes, S ⊢ti* tableinsts ∈ tabletypes) ->

      S = {|
        S_funcs := funcinsts;
        S_tables := tableinsts;
      |} ->
      ⊢S S ok


(* ----------------------------------------------------------------- *)
(** *** Function Instances *)

with valid_funcinst : store -> funcinst -> functype -> Prop :=

  | VFI: forall S C ft mi f,
        ⊢ft ft ok ->
      S ⊢mi mi ∈ C ->  (* TODO: consider change to [exists C] not sure any diff *)
      C ⊢f f ∈ ft ->
      S ⊢fi {| FI_type__wasm := ft; FI_module := mi; FI_code := f |} ∈ ft


(** This is not explicitly defined but occured as

      (⊢ funcinst : functype)*
*)
with valid_funcinsts : store -> list funcinst -> list functype -> Prop :=

  | VFIS: forall S fis fts,
      Forall2 (fun funcinst functype => S ⊢fi funcinst ∈ functype) fis fts ->  
      S ⊢fi* fis ∈ fts


(* ----------------------------------------------------------------- *)
(** *** Host Function Instances *)

(* ----------------------------------------------------------------- *)
(** *** Table Instances *)
(*
   We fixed this rule of core spec: https://webassembly.github.io/spec/core/appendix/properties.html
   but multi-value is still not merge yet.
*)

with valid_tableinst : store -> tableinst -> tabletype -> Prop :=

  | VTI: forall S (fes : list funcelem) n m__opt, 

      length fes = n ->
      (exists fts, S ⊢fe* fes ∈ fts) ->
      ⊢l {| L_min := n; L_max := m__opt |} ∈ I32.max ->
      S ⊢ti {|
          TI_elem := fes;
          TI_max  := m__opt;
        |} ∈ ({| L_min := n; L_max := m__opt |}, funcref)


(** This is not explicitly defined but occured as

      (⊢ tableinst : tabletype)*
*)
with valid_tableinsts : store -> list tableinst -> list tabletype -> Prop :=

  | VTIS: forall S tis tts,
      Forall2 (fun tableinst tabletype => S ⊢ti tableinst ∈ tabletype) tis tts ->  
      S ⊢ti* tis ∈ tts


(* ----------------------------------------------------------------- *)
(** *** Memory Instances *)

with valid_meminst : store -> meminst -> memtype -> Prop :=

  | VMEI: forall S bs n m__opt,
      length bs = n ->
      ⊢l {| L_min := n; L_max := m__opt |} ∈ I32.max16 ->
      S ⊢mei {|
              MEI_data := bs;
              MEI_max := m__opt
            |} ∈ {| L_min := n; L_max := m__opt |}


(* ----------------------------------------------------------------- *)
(** *** Global Instances *)

with valid_globalinst : store -> globalinst -> globaltype -> Prop :=

  | VGI: forall S val mut,
      let t := type_of val in
      S ⊢gi {|
              GI_value := val;
              GI_mut := mut;
            |} ∈ (mut, t)


(* ----------------------------------------------------------------- *)
(** *** Export Instances *)

with valid_exportinst : store -> exportinst -> Prop :=

  | VEXI: forall S ev name,
      (exists et, S ⊢ev ev ∈ et) ->
      S ⊢exi {|
              EXI_name := name;
              EXI_value := ev;
            |} ok

(* ----------------------------------------------------------------- *)
(** *** Module Instances *)

(* Isabelle defines      `funci_agree fs n f = (n < length fs ∧ fs!n = f)`
   and used              `list_all (funci_agree (s_funcs 𝒮)) fs tfs`
   in                    `inst_typing 𝒮 ⦇types = ts, funcs = fs ...⦈ ⦇types_t = ts, func_t = tfs ...⦈`

   which allow the store to be bigger than the module and context.
   this rule actualy merge the "cl_typing" into "inst_typing"

   --------------------------------------------------------------------
   It's important to note that in the WASM spec, ignoring a field of context,
   it doesn't mean "we don't care" (i.e. subtyping), but meaning empty (i.e. ϵ).

   See: https://webassembly.github.io/multi-value/core/valid/conventions.html#contexts
   "When spelling out a context, empty fields are omitted."
*)

with valid_moduleinst : store -> moduleinst -> context -> Prop :=

  | VMI: forall S C fts fts' tts fas tas,
      ⊢ft* fts ok ->

      (* extern check for func/table/mem/global addr *)
      S ⊢fa* fas ∈ fts' ->
      S ⊢ta* tas ∈ tts ->

      S ⊢mi {|
              MI_types := fts;
              MI_funcaddrs := fas;
              MI_tableaddrs := tas;
            |} ∈ {|
                   C_types := fts;
                   C_funcs := fts';
                   C_tables := tts;
                   C_locals := [];
                   C_labels := [];
                   C_return := None;
                 |}

where "  '⊢S' S 'ok' " := (valid_store S)
  and "S '⊢fi' fi '∈' ft"  := (valid_funcinst S fi ft)
  and "S '⊢fi*' fis ∈ fts" := (valid_funcinsts S fis fts)
  and "S '⊢ti' ti ∈ tt" := (valid_tableinst S ti tt)
  and "S '⊢ti*' tis ∈ tts" := (valid_tableinsts S tis tts)
  and "S '⊢mei' mei '∈' met"  := (valid_meminst S mei met)
  and "S '⊢gi' gi '∈' gt"  := (valid_globalinst S gi gt)
  and "S '⊢exi' exi 'ok'"  := (valid_exportinst S exi)
  and "S '⊢mi' Mi '∈' C"  := (valid_moduleinst S Mi C).

Hint Constructors valid_store.
Hint Constructors valid_funcinst.
Hint Constructors valid_funcinsts.
Hint Constructors valid_tableinst.
Hint Constructors valid_tableinsts.
Hint Constructors valid_meminst.
Hint Constructors valid_globalinst.
Hint Constructors valid_exportinst.
Hint Constructors valid_moduleinst.



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

  | VT: forall S F C (rt__opt : option resulttype) ainstrs rt, 
      S ⊢A F ∈ C ->
      (S, C with_return = rt__opt) ⊢a* ainstrs ∈ [] --> rt ->
      (match rt__opt with None => True | Some rt' => rt' = rt end) ->
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

  (* | VAI_invoke : forall S C fa ts1 ts2, *)
  (*     (* TODO: external check *)
  (*        (assume internal always success?) *) *)
  (*     (S,C) ⊢a Invoke fa ∈ ts1 --> ts2 *)

  (* One weird things are the below two are valid against 'ok'... *)
  (* | VAI_init_elem *)
  (* | VAI_init_data *)

  | VAI_label : forall S C n ainstrs0 ainstrs ts1 ts2,
      (* https://github.com/WebAssembly/multi-value/pull/35 *)
      length ts1 = n ->
      (S,C) ⊢a* ainstrs0 ∈ ts1 --> ts2 ->
      (S,(C,labels ts1)) ⊢a* ainstrs ∈ [] --> ts2 ->
      (S,C) ⊢a Label n ainstrs0 ainstrs ∈ [] --> ts2

  (* | VAI_frame : forall S C ainstrs ts n F, *)
  (*     length ts = n -> *)
  (*     (S, Some ts) ⊢T (F, ainstrs) ∈ ts -> *)
  (*     (S,C) ⊢a Frame n F ainstrs ∈ [] --> ts *)


with valid_admin_instrs : store * context -> list admin_instr -> functype -> Prop :=

(* I was naively doing below but it's obviously wrong. 

    | VAIS: forall S C (instrs : list instr) ft,
        C ⊢* instrs ∈ ft ->
        (S,C) ⊢a* ↑instrs ∈ ft

   The possible correct way is to _duplicate_ the [valid_instrs] pattern?
*)

  | VAIS_empty : forall S C ts,
      (S,C) ⊢a* [] ∈ ts --> ts

  | VAIS_snoc : forall S C ainstrs ainstr__N ts0 ts1 ts ts3,
      (S,C) ⊢a* ainstrs ∈ ts1 --> (ts0 ++ ts) (* ts2 *) ->
      (S,C) ⊢a  ainstr__N ∈ ts --> ts3 ->
      (S,C) ⊢a* ainstrs ++ [ainstr__N] ∈ ts1 --> (ts0 ++ ts3)

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

Reserved Notation "⊢mei mei1 '⪯' mei2 " (at level 70).
Inductive extend_meminst : meminst -> meminst -> Prop :=

  | EMEI: forall bs1 bs2 n1 n2 m__opt,
      length bs1 = n1 ->
      length bs2 = n2 ->
      n1 <= n2 ->
      ⊢mei {| MEI_data := bs1; MEI_max := m__opt |}
         ⪯ {| MEI_data := bs2; MEI_max := m__opt |}

where "⊢mei mei1 '⪯' mei2 " := (extend_meminst mei1 mei2).
Hint Constructors extend_meminst.

(* ----------------------------------------------------------------- *)
(** *** Global Instance *)
(**
    the spec defined as same [t] and [c1 = c2],
    we simply defined as same [val].
 *)

Reserved Notation "⊢gi gi1 '⪯' gi2 " (at level 70).
Inductive extend_globalinst : globalinst -> globalinst -> Prop :=

  | EGI: forall val,
      ⊢gi {| GI_value := val; GI_mut := GT_var |}
        ⪯ {| GI_value := val; GI_mut := GT_var |}

where "⊢gi gi1 '⪯' gi2 " := (extend_globalinst gi1 gi2).
Hint Constructors extend_globalinst.

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


(* ================================================================= *)
(** ** Lemmas *)

(* ----------------------------------------------------------------- *)
(** *** Extension Refl *)

(* Extending funcinsts relation only holds as reflexivity. *)
Lemma extend_funcinsts_refl: forall fis fis',
    ⊢fi* fis ⪯ fis' <->
    fis = fis'.
Proof with auto.
  split.
  - (* -> *) 
    introv HEFIS.
    inverts HEFIS as HForall2.
    induction HForall2; try inverts H; subst...
  - (* <- *)
    introv Heq; subst.
    induction fis'.
    + constructor; constructor.
    + constructor. constructor. constructor. inverts IHfis'...
Qed.

(* Weaker than [extend_funcinst_refl] by only implying [<-] direction *)
Lemma extend_tableinst_refl: forall ti,
    ⊢ti ti ⪯ ti. 
Proof with auto.
  intros.
  destruct ti eqn:Heqti.
  rename TI_elem into elems.
  remember (length elems) as n.
  econstructor;
   try (symmetry; eassumption)...
Qed.

Lemma extend_tableinsts_refl: forall tis,
    ⊢ti* tis ⪯ tis. 
Proof with auto.
  intros.
  constructor.
  induction tis; constructor.
  - apply extend_tableinst_refl.
  - apply IHtis.
Qed.

Lemma extend_store_refl: forall S,
    ⊢S S ok ->
    ⊢S S ⪯ S.
Proof with auto.
  introv HSok.
  inverts HSok as HVFIS HVTIS.
  econstructor; auto.
  - instantiate (1 := []); instantiate (1 := funcinsts). symmetry; apply app_nil_r...
  - constructor; simpl.
    assert (Heq : funcinsts = funcinsts). reflexivity.
    apply (extend_funcinsts_refl funcinsts funcinsts) in Heq.
    inverts Heq...
  - instantiate (1 := []); instantiate (1 := tableinsts). symmetry; apply app_nil_r...
  - constructor; simpl.
    specialize (extend_tableinsts_refl tableinsts). intros Heq.
    inverts Heq...
Qed.
