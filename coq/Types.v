(* ***************************************************************** *)
(* Types.v                                                           *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)


(* ################################################################# *)
(** * Types *)

(* It's interesting that if we use

     Require Export Int.
     Require Export Float.

   Here, we will later hit errors in [Execution.v] saying:
 
     (cannot unify "I32.t" and "Values.I32.t").

   This might be a bug or intentional of Coq.
   Issue posted: https://github.com/coq/coq/issues/10869
 *)

From Wasm Require Import Int.
From Wasm Require Import Float.
From Wasm Require Export Commons.

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

  Example ex1 : all_valtype [T_i32] T_i32 = true. auto. Qed.

End TestValtypeEq.
  

(* ----------------------------------------------------------------- *)
(** *** Result Types *)

(** the current spec use optional occurence such as

      Definition resulttype : Type := option valtype.

    while we moved to the "multi-value" proposal where

      resulttype ::= [vec(valtype)]

    See option valtype section below.
 *)

Notation resulttype := (list valtype). 



(* ----------------------------------------------------------------- *)
(** *** Function Types *)

Record functype :=
  {
    FT_ins  : resulttype;
    FT_outs : resulttype;
  }.

Module FunctypeNotations.

  Notation "ts1 --> ts2" :=
    ({| FT_ins := ts1; FT_outs := ts2|})
    (at level 30, right associativity) : wasm_scope.
  Open Scope wasm_scope.

End FunctypeNotations.


(** Testing *)

Module TypesTest.

  Example ex_res1: resulttype := [].
  Example ex_res2: resulttype := [T_i32].
  Example ex_fun: functype := {| FT_ins := [T_i32]; FT_outs := [T_i32] |}.

  (* Func Notation Testing *)

  Import FunctypeNotations.

  Example ex_fun_nu : functype := [] --> [T_i32].

  Example ex_fun_un : functype := [T_i32] --> [T_i32].

  Example ex_fun_bin : functype := [T_i32; T_i32] --> [T_i32].

  (* cannot looser than ++ *)
  Example ex_fun_loose : functype := ([T_i32] ++ [T_i32]) --> [T_i32].

End TypesTest.


(* ----------------------------------------------------------------- *)
(** *** Limits *)

(* techinically the spec use [u32], which mean we should interpter
   this [I32.t] as unsigned integers. *)

Record limits := 
  {
    L_min: Int.I32.t;
    L_max: option Int.I32.t;
  }.

(* ----------------------------------------------------------------- *)
(** *** Memory Types *)

Definition memtype := limits.


(* ----------------------------------------------------------------- *)
(** *** Table Types *)

(* according to spec:

   > The element type [funcref] is the infinite union of all function types.
     A table of that type thus contains references to functions of
     heterogeneous type.

   the [Call_indirect] will fetch index into this table,
   and the type of function is **checked dynamically**

   combined it can represent *function pointer* and dynamic linking.
 *)

(* We don't need ET since [funcref] is a unique name. *)
Inductive elemtype := funcref.

Definition tabletype : Type := limits * elemtype.


(* ----------------------------------------------------------------- *)
(** *** Global Types *)

Inductive mut :=
  | GT_const
  | GT_var.

Definition globaltype : Type := mut * valtype.


(* ----------------------------------------------------------------- *)
(** *** External Types *)

Inductive externtype :=
  | ET_func (ft: functype)
  | ET_table (tt: tabletype)
  | ET_mem (mt: memtype)
  | ET_global (gt: globaltype).


(* ----------------------------------------------------------------- *)
(** *** Option ValType Occurence *)

(* Not currently used in favor of plain [option value]
   Potential uses would be [blocktype] and module [M_return].
 *)

Definition opt_valtype := (option valtype).

Definition opt_to_rt (opt : opt_valtype) : resulttype :=
  match opt with
  | Some valtype => [valtype]
  | None => []
  end.

Coercion opt_to_rt : opt_valtype >-> resulttype.

Module OptionValTyTest.

  Import FunctypeNotations.

  Example valtype1 : opt_valtype := Some T_i32.
  Example valtype2 : opt_valtype := None.

  Example ft_some := [] --> opt_to_rt valtype1.
  Example ft_some2 := [] --> valtype1.

End OptionValTyTest.
