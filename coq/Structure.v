(* ***************************************************************** *)
(* Structure.v                                                       *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)


(* ################################################################# *)
(** * Structure *)

From Coq Require Export Lists.List.
Export ListNotations.

(** Module Type, Signature.. **)
From Coq Require Export Structures.Equalities.

(* ================================================================= *)
(** ** Modules (Pre) *)


(* ----------------------------------------------------------------- *)
(** *** Indices *)

Definition typeidx := nat.
Definition funcidx := nat.
Definition tableidx := nat.
Definition memidx := nat.
Definition globalidx := nat.
Definition localidx := nat.
Definition labelidx := nat.



(* ================================================================= *)
(** ** Values *)

Parameter byte : Type.

Parameter i8 : Type.
Parameter i16 : Type.
Parameter i32 : Type.
Parameter i64 : Type.

Parameter u32 : Type.
Parameter u64 : Type.

Parameter s32 : Type.
Parameter s64 : Type.

Parameter f32 : Type.
Parameter f64 : Type.


(* ================================================================= *)
(** ** Types *)

(* ----------------------------------------------------------------- *)
(** *** Value Types *)

Inductive valtype :=
  | T_i32
  | T_i64
  | T_f32
  | T_f64.

Definition eqb_valtype (ty1 ty2: valtype) : bool :=
  match ty1, ty2 with
  | T_i32, T_i32 => true
  | T_i64, T_i64 => true
  | T_f32, T_f32 => true
  | T_f64, T_f64 => true
  | _, _ => false
  end.

Definition all_valtype (ts: list valtype) (t': valtype) :=
  forallb (fun t => eqb_valtype t t') ts.

Lemma eqb_valtype_refl : forall (ty: valtype),
  eqb_valtype ty ty = true.
Proof.
  destruct ty; auto.
Qed.

Lemma eqb_valtype_eq : forall (ty1 ty2: valtype),
  eqb_valtype ty1 ty2 = true -> ty1 = ty2.
Proof with eauto.
  intro ty1.
  destruct ty1;
    intros ty2 Heqb;
    destruct ty2; inversion Heqb...
Qed.

(** Having eq_dec is equivalent to having eqb and its spec
    How? https://coq.inria.fr/library/Coq.Structures.Equalities.html
  *)
Lemma valtype_eq_dec: forall (ty1 ty2: valtype), {ty1 = ty2} + {ty1 <> ty2}.
Proof.
  decide equality.
Qed.


Module TestValtypeEq.

Compute (all_valtype [T_i32] T_i32).

Definition ex1 (ty: valtype) := if valtype_eq_dec ty T_i32 then true else false.

Compute (ex1 T_i32).

Lemma ex2: ex1(T_i32) = true.
Proof.
  Abort.


End TestValtypeEq.
  
(* ----------------------------------------------------------------- *)
(** *** Result Types *)

(* Definition resulttype : Type := option valtype.  *)

Notation resulttype := (list valtype). 

(* ----------------------------------------------------------------- *)
(** *** Function Types *)

Record functype :=
  {
    ta: list valtype;
    tr: list valtype
  }.

Module FunctypeNotations.
Notation "t1 --> t2" :=
  ({| ta := t1; tr := t2|})
  (at level 30, right associativity) : wasm_scope.
Open Scope wasm_scope.
End FunctypeNotations.

(** Coercion into sum type *)

(** N.B. It seems like 

      Definition ty := functype

    during the actual validations?
 *)

Inductive ty :=
  | T_val (_: valtype)
  | T_res (_: resulttype)
  | T_fun (_: functype).

Coercion T_val : valtype >-> ty.
Coercion T_fun : functype >-> ty.


(** Testing *)

Module TypesTest.

  Definition ex_res1: resulttype := [].
  Definition ex_res2: resulttype := [T_i32].
  Definition ex_fun: functype := {| ta := [T_i32]; tr := [T_i32] |}.

  (* Coercion Testing *)

  Definition ex_res1_ty_c : ty := T_res [].
  Definition ex_res2_ty_c : ty := T_res [T_i32].
  Definition ex_fun_ty_c : ty := {| ta := [T_i32]; tr := [T_i32] |}.

  (* Func Notation Testing *)

  Import FunctypeNotations.

  Definition ex_fun_nu : functype := [] --> [T_i32].
  Definition ex_fun_nu_ty_c : ty := [] --> [T_i32].
  Compute ex_fun_nu.
  Compute ex_fun_nu_ty_c.

  Definition ex_fun_un : functype := [T_i32] --> [T_i32].
  Definition ex_fun_un_ty_c : ty := [T_i32] --> [T_i32].
  Compute ex_fun_un.
  Compute ex_fun_un_ty_c.

  Definition ex_fun_bin : functype := [T_i32; T_i32] --> [T_i32].
  Definition ex_fun_bin_ty_c : ty := [T_i32; T_i32] --> [T_i32].
  Compute ex_fun_bin.
  Compute ex_fun_bin_ty_c.

  (* cannot looser than ++ *)
  Definition ex_fun_loose : functype := ([T_i32] ++ [T_i32]) --> [T_i32].

  Definition ex_fun_with_res_c : ty := [T_i32; T_i32] --> ex_res2.
  Compute ex_fun_with_res_c.

End TypesTest.


(* ================================================================= *)
(** ** Instruction *)

(** nn, mm

    the set of possible rewritting result is

      {i32, i64, f32, f64}

    which is isomorphic with the valtype. so we can safely use valtype as the constraint when defining instructions.
 *)

Definition valOf (v: valtype) : Type :=
  match v with
  | T_i32 => i32
  | T_i64 => i64
  | T_f32 => f32
  | T_f64 => f64
  end.

(** unsigned or signed *)

Inductive sx :=
  | u
  | s.

(** int unary operator *)

Inductive _iunop :=
  | clz
  | ctz
  | popcnt.

(** int binary operator *)

Inductive _ibinop := 
  | add
  | sub
  | mul
  | div (_: sx)
  | rem (_: sx)
  | and
  | or
  | xor
  | shl
  | shr : sx -> _ibinop
  | rotl
  | rotr.

(** int tests operator *)

Inductive _itestop :=
  | eqz.

(** int relational operator *)

Inductive _irelop :=
  | eq
  | ne
  | lt (_: sx)
  | gt (_: sx)
  | le (_: sx)
  | ge (_: sx).


Inductive instr :=
(* ----------------------------------------------------------------- *)
(** *** Numeric Instruction *)
  | const (t: valtype) (c : valOf t)
  | iunop : valtype -> _iunop -> instr
  | ibinop : valtype -> _ibinop -> instr
  | itestop : valtype -> _itestop -> instr
  | irelop : valtype -> _irelop -> instr

(* ----------------------------------------------------------------- *)
(** *** Parametric Instruction *)
  | drop
  | select

(* ----------------------------------------------------------------- *)
(** *** Variable Instruction *)
  | local_get (i: localidx)
  | local_set (i: localidx)
  | local_tee (i: localidx)
  (* | global_get (i: globalidx) *)
  (* | global_set (i: globalidx) *)

(* ----------------------------------------------------------------- *)
(** *** Memory Instruction *)

(* ----------------------------------------------------------------- *)
(** *** Control Instructions *)
  | nop
  | unreachable
  | block : resulttype -> list instr -> instr
  | loop : resulttype -> list instr -> instr
  | if' : resulttype -> list instr -> list instr -> instr
  | br : labelidx -> instr
  | br_if : labelidx -> instr
  | br_table : list labelidx -> labelidx -> instr
  | return'
  | call : funcidx -> instr
  | call_indirect : typeidx -> instr.
    

Definition expr : Type := list instr.


(* ================================================================= *)
(** ** Modules (Post) *)


(* ----------------------------------------------------------------- *)
(** *** Functions *)

Record func :=
  {
    type : typeidx;
    locals : list valtype;
    body: expr;
  }.


(* ----------------------------------------------------------------- *)
(** *** Module *)

Record module :=
  {
    types : list functype;
    funcs : list func;
  }.

                  

