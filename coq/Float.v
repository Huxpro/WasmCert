(* ***************************************************************** *)
(* Float.v                                                           *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)


(* ################################################################# *)
(** * Float  *)

From Coq Require Import ZArith Lia.
From Flocq Require Import IEEE754.Binary IEEE754.Bits.

(* ----------------------------------------------------------------- *)
(** *** Value representation *)

(** Floats are IEEE 754 binary floats from the Flocq library, described by
    their mantissa width [mw] and exponent width [ew]. *)

Module Type Rep.
  Parameter bitwidth: nat.
  Parameter mw ew : Z.
  Parameter Hmw : (0 < mw)%Z.
  Parameter Hew : (0 < ew)%Z.
  Parameter Hmax : (mw + 1 < 2 ^ (ew - 1))%Z.
  (* The positive canonical NaN, i.e. with only the quiet bit set. *)
  Parameter canonical_nan :
    { x : binary_float (mw + 1) (2 ^ (ew - 1)) | is_nan _ _ x = true }.
End Rep.

Module Rep32 <: Rep.
  Definition bitwidth := 32%nat.
  Definition mw := 23%Z.
  Definition ew := 8%Z.
  Lemma Hmw : (0 < mw)%Z. Proof. reflexivity. Qed.
  Lemma Hew : (0 < ew)%Z. Proof. reflexivity. Qed.
  Lemma Hmax : (mw + 1 < 2 ^ (ew - 1))%Z. Proof. reflexivity. Qed.
  Definition canonical_nan := default_nan_pl32.
End Rep32.

Module Rep64 <: Rep.
  Definition bitwidth := 64%nat.
  Definition mw := 52%Z.
  Definition ew := 11%Z.
  Lemma Hmw : (0 < mw)%Z. Proof. reflexivity. Qed.
  Lemma Hew : (0 < ew)%Z. Proof. reflexivity. Qed.
  Lemma Hmax : (mw + 1 < 2 ^ (ew - 1))%Z. Proof. reflexivity. Qed.
  Definition canonical_nan := default_nan_pl64.
End Rep64.


(* ----------------------------------------------------------------- *)
(** *** Functor *)

Module Type S.
  Parameter t : Type.
  Parameter bitwidth: nat.

  Parameter zero : t.

  (* funop *)
  Parameter abs : t -> option t.
  Parameter neg : t -> option t.
  Parameter sqrt : t -> option t.
  Parameter ceil : t -> option t.
  Parameter floor : t -> option t.
  Parameter trunc : t -> option t.
  Parameter nearest : t -> option t.

  (* fbinop *)
  Parameter add : t -> t -> option t.
  Parameter sub : t -> t -> option t.
  Parameter mul : t -> t -> option t.
  Parameter div : t -> t -> option t.
  Parameter min : t -> t -> option t.
  Parameter max : t -> t -> option t.
  Parameter copysign : t -> t -> option t.

  (* fretop *)
  Parameter eq : t -> t -> bool.
  Parameter ne : t -> t -> bool.
  Parameter lt : t -> t -> bool.
  Parameter gt : t -> t -> bool.
  Parameter le : t -> t -> bool.
  Parameter ge : t -> t -> bool.

  (* axioms *)
End S.

(* ----------------------------------------------------------------- *)
(** *** Implementation *)

(** Following the spec's numerics
    (https://webassembly.github.io/spec/core/exec/numerics.html):

    - Arithmetic rounds to nearest, ties to even. Where the spec allows
      a set of NaN results, we always return the positive canonical NaN,
      which is a member of every such set.
    - [abs], [neg] and [copysign] only act on the sign bit, preserving
      NaN payloads.
    - [min]/[max] return a NaN if either operand is one, and order
      [-0] below [+0].
    - Comparisons are false on NaNs, except [ne].

    None of the float operations trap, so they all return [Some].
 *)

Module Make (R: Rep) <: S.
  Definition bitwidth := R.bitwidth.

  Definition prec : Z := (R.mw + 1)%Z.
  Definition emax : Z := (2 ^ (R.ew - 1))%Z.

  Definition t := binary_float prec emax.

  Lemma Hprec : FLX.Prec_gt_0 prec.
  Proof. unfold FLX.Prec_gt_0, prec. pose proof R.Hmw. lia. Qed.

  Lemma Hprec_emax : BinarySingleNaN.Prec_lt_emax prec emax.
  Proof. exact R.Hmax. Qed.

  Definition nan : t := proj1_sig R.canonical_nan.
  Definition unop_nan (_: t) := R.canonical_nan.
  Definition binop_nan (_ _: t) := R.canonical_nan.

  Definition zero : t := B754_zero _ _ false.

  (* Bit patterns *)
  Definition to_bits (x: t) : Z := bits_of_binary_float R.mw R.ew x.
  Definition of_bits (z: Z) : t := binary_float_of_bits R.mw R.ew R.Hmw R.Hew R.Hmax z.
  Definition sign_bit : Z := (2 ^ (R.mw + R.ew))%Z.

  (* funop *)
  Definition abs (x: t) : option t :=
    Some (of_bits (Z.land (to_bits x) (sign_bit - 1))).
  Definition neg (x: t) : option t :=
    Some (of_bits (Z.lxor (to_bits x) sign_bit)).
  Definition sqrt (x: t) : option t :=
    Some (Bsqrt prec emax Hprec Hprec_emax unop_nan BinarySingleNaN.mode_NE x).
  Definition ceil (x: t) : option t :=
    Some (Bnearbyint prec emax Hprec_emax unop_nan BinarySingleNaN.mode_UP x).
  Definition floor (x: t) : option t :=
    Some (Bnearbyint prec emax Hprec_emax unop_nan BinarySingleNaN.mode_DN x).
  Definition trunc (x: t) : option t :=
    Some (Bnearbyint prec emax Hprec_emax unop_nan BinarySingleNaN.mode_ZR x).
  Definition nearest (x: t) : option t :=
    Some (Bnearbyint prec emax Hprec_emax unop_nan BinarySingleNaN.mode_NE x).

  (* fbinop *)
  Definition add (x y: t) : option t :=
    Some (Bplus prec emax Hprec Hprec_emax binop_nan BinarySingleNaN.mode_NE x y).
  Definition sub (x y: t) : option t :=
    Some (Bminus prec emax Hprec Hprec_emax binop_nan BinarySingleNaN.mode_NE x y).
  Definition mul (x y: t) : option t :=
    Some (Bmult prec emax Hprec Hprec_emax binop_nan BinarySingleNaN.mode_NE x y).
  Definition div (x y: t) : option t :=
    Some (Bdiv prec emax Hprec Hprec_emax binop_nan BinarySingleNaN.mode_NE x y).

  Definition min (x y: t) : option t :=
    if orb (is_nan _ _ x) (is_nan _ _ y) then Some nan else
    match Bcompare _ _ x y with
    | Some Lt => Some x
    | Some Gt => Some y
    | Some Eq => Some (if Bsign _ _ x then x else y)  (* -0 < +0 *)
    | None => Some nan
    end.

  Definition max (x y: t) : option t :=
    if orb (is_nan _ _ x) (is_nan _ _ y) then Some nan else
    match Bcompare _ _ x y with
    | Some Lt => Some y
    | Some Gt => Some x
    | Some Eq => Some (if Bsign _ _ x then y else x)  (* -0 < +0 *)
    | None => Some nan
    end.

  Definition copysign (x y: t) : option t :=
    Some (of_bits (Z.lor (Z.land (to_bits x) (sign_bit - 1))
                         (Z.land (to_bits y) sign_bit))).

  (* frelop *)
  Definition cmp (x y: t) : option comparison := Bcompare _ _ x y.

  Definition eq (x y: t) : bool :=
    match cmp x y with Some Eq => true | _ => false end.
  Definition ne (x y: t) : bool := negb (eq x y).
  Definition lt (x y: t) : bool :=
    match cmp x y with Some Lt => true | _ => false end.
  Definition gt (x y: t) : bool :=
    match cmp x y with Some Gt => true | _ => false end.
  Definition le (x y: t) : bool :=
    match cmp x y with Some Lt | Some Eq => true | _ => false end.
  Definition ge (x y: t) : bool :=
    match cmp x y with Some Gt | Some Eq => true | _ => false end.

End Make.


(* ----------------------------------------------------------------- *)
(** *** Make *)

Module F32 := Float.Make(Rep32).
Module F64 := Float.Make(Rep64).


(* ----------------------------------------------------------------- *)
(** *** Tests against the spec *)

Module FloatTest.

  Definition f32 (z: Z) : F32.t := F32.of_bits z.
  Definition bits (o: option F32.t) : option Z := option_map F32.to_bits o.

  Definition pos_zero := 0%Z.
  Definition neg_zero := 2147483648%Z.       (* 0x80000000 *)
  Definition one      := 1065353216%Z.       (* 0x3f800000 = 1.0 *)
  Definition two      := 1073741824%Z.       (* 0x40000000 = 2.0 *)
  Definition three    := 1077936128%Z.       (* 0x40400000 = 3.0 *)
  Definition four     := 1082130432%Z.       (* 0x40800000 = 4.0 *)
  Definition m_one    := 3212836864%Z.       (* 0xbf800000 = -1.0 *)
  Definition half     := 1056964608%Z.       (* 0x3f000000 = 0.5 *)
  Definition m_half   := 3204448256%Z.       (* 0xbf000000 = -0.5 *)
  Definition m_1_5    := 3217031168%Z.       (* 0xbfc00000 = -1.5 *)
  Definition two_5    := 1075838976%Z.       (* 0x40200000 = 2.5 *)
  Definition three_5  := 1080033280%Z.       (* 0x40600000 = 3.5 *)
  Definition cnan     := 2143289344%Z.       (* 0x7fc00000, canonical NaN *)
  Definition nan_pl   := 2143289345%Z.       (* 0x7fc00001 *)
  Definition m_nan_pl := 4290772993%Z.       (* 0xffc00001 *)

  Example add_1_2 : bits (F32.add (f32 one) (f32 two)) = Some three.
  Proof. vm_compute. reflexivity. Qed.
  Example add_nan : bits (F32.add (f32 nan_pl) (f32 one)) = Some cnan.
  Proof. vm_compute. reflexivity. Qed.
  Example sqrt_neg : bits (F32.sqrt (f32 m_one)) = Some cnan.
  Proof. vm_compute. reflexivity. Qed.

  (* Sign operations are bitwise and keep NaN payloads *)
  Example neg_zero_ : bits (F32.neg (f32 pos_zero)) = Some neg_zero.
  Proof. vm_compute. reflexivity. Qed.
  Example neg_nan : bits (F32.neg (f32 nan_pl)) = Some m_nan_pl.
  Proof. vm_compute. reflexivity. Qed.
  Example abs_nan : bits (F32.abs (f32 m_nan_pl)) = Some nan_pl.
  Proof. vm_compute. reflexivity. Qed.
  Example copysign_ : bits (F32.copysign (f32 one) (f32 neg_zero)) = Some m_one.
  Proof. vm_compute. reflexivity. Qed.

  (* min/max order -0 below +0 and propagate NaN *)
  Example min_zeros : bits (F32.min (f32 pos_zero) (f32 neg_zero)) = Some neg_zero.
  Proof. vm_compute. reflexivity. Qed.
  Example max_zeros : bits (F32.max (f32 neg_zero) (f32 pos_zero)) = Some pos_zero.
  Proof. vm_compute. reflexivity. Qed.
  Example min_nan : bits (F32.min (f32 one) (f32 nan_pl)) = Some cnan.
  Proof. vm_compute. reflexivity. Qed.

  (* Rounding to integers *)
  Example nearest_even_down : bits (F32.nearest (f32 two_5)) = Some two.
  Proof. vm_compute. reflexivity. Qed.
  Example nearest_even_up : bits (F32.nearest (f32 three_5)) = Some four.
  Proof. vm_compute. reflexivity. Qed.
  Example trunc_neg : bits (F32.trunc (f32 m_1_5)) = Some m_one.
  Proof. vm_compute. reflexivity. Qed.
  Example ceil_neg_half : bits (F32.ceil (f32 m_half)) = Some neg_zero.
  Proof. vm_compute. reflexivity. Qed.
  Example floor_neg_half : bits (F32.floor (f32 m_half)) = Some m_one.
  Proof. vm_compute. reflexivity. Qed.
  Example floor_half : bits (F32.floor (f32 half)) = Some pos_zero.
  Proof. vm_compute. reflexivity. Qed.

  (* Comparisons *)
  Example eq_zeros : F32.eq (f32 pos_zero) (f32 neg_zero) = true.
  Proof. vm_compute. reflexivity. Qed.
  Example lt_nan : F32.lt (f32 cnan) (f32 one) = false.
  Proof. vm_compute. reflexivity. Qed.
  Example eq_nan : F32.eq (f32 cnan) (f32 cnan) = false.
  Proof. vm_compute. reflexivity. Qed.
  Example ne_nan : F32.ne (f32 cnan) (f32 cnan) = true.
  Proof. vm_compute. reflexivity. Qed.

  (* binary64 *)
  Example add64_1_2 :
    option_map F64.to_bits (F64.add (F64.of_bits 4607182418800017408%Z)   (* 1.0 *)
                                    (F64.of_bits 4611686018427387904%Z))  (* 2.0 *)
    = Some 4613937818241073152%Z.                                        (* 3.0 *)
  Proof. vm_compute. reflexivity. Qed.

End FloatTest.
