(* ***************************************************************** *)
(* Int.v                                                             *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)


(* ################################################################# *)
(** * Int  *)

From Coq Require Import ZArith Lia.
Local Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(** *** Value representation *)

Module Type Rep.
  Parameter bitwidth: nat.
End Rep.

Module Rep32.
  Definition bitwidth := 32%nat.
End Rep32.

Module Rep64.
  Definition bitwidth := 64%nat.
End Rep64.


(* ----------------------------------------------------------------- *)
(** *** Functor *)

Module Type S.
  Parameter t : Type.
  Parameter bitwidth: nat.

  Parameter zero : t.
  Parameter one : t.
  Parameter min : t.
  Parameter max : t.
  Parameter max16 : t.

  Parameter from_nat : nat -> t.
  Parameter to_nat : t -> nat.

  (* iunop *)
  Parameter clz    : t -> option t.
  Parameter ctz    : t -> option t.
  Parameter popcnt : t -> option t.

  (* ibinop *)
  Parameter add   : t -> t -> option t.
  Parameter sub   : t -> t -> option t.
  Parameter mul   : t -> t -> option t.
  Parameter div_s : t -> t -> option t.
  Parameter div_u : t -> t -> option t.
  Parameter rem_s : t -> t -> option t.
  Parameter rem_u : t -> t -> option t.
  Parameter and   : t -> t -> option t.
  Parameter or    : t -> t -> option t.
  Parameter xor   : t -> t -> option t.
  Parameter shl   : t -> t -> option t.
  Parameter shr_s : t -> t -> option t.
  Parameter shr_u : t -> t -> option t.
  Parameter rotl  : t -> t -> option t.
  Parameter rotr  : t -> t -> option t.

  (* itestop *)
  Parameter eqz : t -> bool.

  (* iretop *)
  Parameter eq   : t -> t -> bool.
  Parameter ne   : t -> t -> bool.
  Parameter lt_s : t -> t -> bool.
  Parameter lt_u : t -> t -> bool.
  Parameter gt_s : t -> t -> bool.
  Parameter gt_u : t -> t -> bool.
  Parameter le_s : t -> t -> bool.
  Parameter le_u : t -> t -> bool.
  Parameter ge_s : t -> t -> bool.
  Parameter ge_u : t -> t -> bool.

  (* axioms *)
End S.


(* ----------------------------------------------------------------- *)
(** *** Implementation *)

(** Integers are represented as their unsigned value in [[0, 2^N)], as in
    the spec's numerics
    (https://webassembly.github.io/spec/core/exec/numerics.html).
    The range is stated with two strict inequalities so that its proofs
    are unique without any axiom, see [eq_of_unsigned].

    Operations return [None] exactly where the spec leaves the result
    undefined, i.e. where execution traps: division and remainder by
    zero, and signed division overflow.
 *)

Module Make (R: Rep) <: S.
  Include R.

  Definition wordsize : Z := Z.of_nat bitwidth.
  Definition modulus : Z := 2 ^ wordsize.
  Definition half_modulus : Z := modulus / 2.

  Lemma modulus_pos : 0 < modulus.
  Proof. apply Z.pow_pos_nonneg; [lia | apply Nat2Z.is_nonneg]. Qed.

  Record int := mkint {
    intval : Z;
    intrange : -1 < intval < modulus;
  }.

  Definition t := int.

  Lemma repr_range : forall z, -1 < z mod modulus < modulus.
  Proof.
    intros z. pose proof (Z.mod_pos_bound z modulus modulus_pos). lia.
  Qed.

  Definition repr (z: Z) : t := mkint (z mod modulus) (repr_range z).
  Definition unsigned (i: t) : Z := intval i.
  Definition signed (i: t) : Z :=
    let u := unsigned i in
    if u <? half_modulus then u else u - modulus.

  Lemma lt_proof_irrelevance : forall (x y: Z) (p q: x < y), p = q.
  Proof.
    intros x y p q.
    apply Eqdep_dec.UIP_dec. decide equality.
  Qed.

  Lemma eq_of_unsigned : forall i j, unsigned i = unsigned j -> i = j.
  Proof.
    intros [i [Hi1 Hi2]] [j [Hj1 Hj2]] Heq. simpl in Heq. subst j.
    f_equal. f_equal; apply lt_proof_irrelevance.
  Qed.

  Definition zero : t := repr 0.
  Definition one : t := repr 1.
  Definition min : t := repr 0.                 (* smallest unsigned value *)
  Definition max : t := repr (modulus - 1).     (* largest unsigned value *)
  Definition max16 : t := repr (2 ^ 16).

  Definition from_nat (n: nat) : t := repr (Z.of_nat n).
  Definition to_nat (i: t) : nat := Z.to_nat (unsigned i).

  (* iunop *)

  (* Number of leading zeros among the lowest [k] bits of [z]. *)
  Fixpoint clz_aux (k: nat) (z: Z) : Z :=
    match k with
    | O => 0
    | Datatypes.S k' => if Z.testbit z (Z.of_nat k') then 0 else 1 + clz_aux k' z
    end.

  (* Number of trailing zeros among the [k] bits of [z] from bit [i] up. *)
  Fixpoint ctz_aux (k: nat) (i: nat) (z: Z) : Z :=
    match k with
    | O => 0
    | Datatypes.S k' => if Z.testbit z (Z.of_nat i) then 0 else 1 + ctz_aux k' (Datatypes.S i) z
    end.

  (* Number of set bits among the lowest [k] bits of [z]. *)
  Fixpoint popcnt_aux (k: nat) (z: Z) : Z :=
    match k with
    | O => 0
    | Datatypes.S k' => (if Z.testbit z (Z.of_nat k') then 1 else 0) + popcnt_aux k' z
    end.

  Definition clz (i: t) : option t := Some (repr (clz_aux bitwidth (unsigned i))).
  Definition ctz (i: t) : option t := Some (repr (ctz_aux bitwidth 0 (unsigned i))).
  Definition popcnt (i: t) : option t := Some (repr (popcnt_aux bitwidth (unsigned i))).

  (* ibinop *)

  Definition add (i j: t) : option t := Some (repr (unsigned i + unsigned j)).
  Definition sub (i j: t) : option t := Some (repr (unsigned i - unsigned j)).
  Definition mul (i j: t) : option t := Some (repr (unsigned i * unsigned j)).

  Definition div_u (i j: t) : option t :=
    if unsigned j =? 0 then None else Some (repr (unsigned i / unsigned j)).

  (* Truncates toward zero; [2^(N-1)] is not representable as a signed result. *)
  Definition div_s (i j: t) : option t :=
    if unsigned j =? 0 then None else
    let q := Z.quot (signed i) (signed j) in
    if q =? half_modulus then None else Some (repr q).

  Definition rem_u (i j: t) : option t :=
    if unsigned j =? 0 then None else Some (repr (unsigned i mod unsigned j)).

  (* The result has the sign of the dividend. *)
  Definition rem_s (i j: t) : option t :=
    if unsigned j =? 0 then None else Some (repr (Z.rem (signed i) (signed j))).

  Definition and (i j: t) : option t := Some (repr (Z.land (unsigned i) (unsigned j))).
  Definition or  (i j: t) : option t := Some (repr (Z.lor  (unsigned i) (unsigned j))).
  Definition xor (i j: t) : option t := Some (repr (Z.lxor (unsigned i) (unsigned j))).

  (* Shift and rotate counts are taken modulo the bit width. *)
  Definition shift_count (j: t) : Z := unsigned j mod wordsize.

  Definition shl (i j: t) : option t :=
    Some (repr (Z.shiftl (unsigned i) (shift_count j))).
  Definition shr_u (i j: t) : option t :=
    Some (repr (Z.shiftr (unsigned i) (shift_count j))).
  Definition shr_s (i j: t) : option t :=
    Some (repr (Z.shiftr (signed i) (shift_count j))).

  Definition rotl (i j: t) : option t :=
    let k := shift_count j in
    Some (repr (Z.lor (Z.shiftl (unsigned i) k) (Z.shiftr (unsigned i) (wordsize - k)))).
  Definition rotr (i j: t) : option t :=
    let k := shift_count j in
    Some (repr (Z.lor (Z.shiftr (unsigned i) k) (Z.shiftl (unsigned i) (wordsize - k)))).

  (* itestop *)
  Definition eqz (i: t) : bool := unsigned i =? 0.

  (* irelop *)
  Definition eq   (i j: t) : bool := unsigned i =? unsigned j.
  Definition ne   (i j: t) : bool := negb (eq i j).
  Definition lt_s (i j: t) : bool := signed i <? signed j.
  Definition lt_u (i j: t) : bool := unsigned i <? unsigned j.
  Definition gt_s (i j: t) : bool := signed j <? signed i.
  Definition gt_u (i j: t) : bool := unsigned j <? unsigned i.
  Definition le_s (i j: t) : bool := signed i <=? signed j.
  Definition le_u (i j: t) : bool := unsigned i <=? unsigned j.
  Definition ge_s (i j: t) : bool := signed j <=? signed i.
  Definition ge_u (i j: t) : bool := unsigned j <=? unsigned i.

End Make.


(* ----------------------------------------------------------------- *)
(** *** Make *)

Module I32 := Int.Make(Rep32).
Module I64 := Int.Make(Rep64).


(* ----------------------------------------------------------------- *)
(** *** Tests against the spec *)

Module IntTest.

  Definition u32 (o: option I32.t) : option Z := option_map I32.unsigned o.
  Definition s32 (o: option I32.t) : option Z := option_map I32.signed o.
  Definition i32 (z: Z) : I32.t := I32.repr z.

  (* Wrap-around *)
  Example add_wrap : u32 (I32.add (i32 (2^32 - 1)) (i32 1)) = Some 0.
  Proof. reflexivity. Qed.
  Example sub_wrap : s32 (I32.sub (i32 0) (i32 1)) = Some (-1).
  Proof. reflexivity. Qed.

  (* Division traps on zero divisor and on signed overflow *)
  Example div_u_zero : I32.div_u (i32 1) (i32 0) = None.
  Proof. reflexivity. Qed.
  Example div_s_overflow : I32.div_s (i32 (- 2^31)) (i32 (-1)) = None.
  Proof. reflexivity. Qed.
  Example div_s_trunc : s32 (I32.div_s (i32 (-7)) (i32 2)) = Some (-3).
  Proof. reflexivity. Qed.
  Example div_u_big : u32 (I32.div_u (i32 (-7)) (i32 2)) = Some 2147483644.
  Proof. reflexivity. Qed.
  Example rem_s_sign : s32 (I32.rem_s (i32 (-7)) (i32 2)) = Some (-1).
  Proof. reflexivity. Qed.
  Example rem_s_overflow : s32 (I32.rem_s (i32 (- 2^31)) (i32 (-1))) = Some 0.
  Proof. reflexivity. Qed.

  (* Shifts and rotations use the count modulo 32 *)
  Example shl_mod : u32 (I32.shl (i32 1) (i32 33)) = Some 2.
  Proof. reflexivity. Qed.
  Example shr_s_neg : s32 (I32.shr_s (i32 (-8)) (i32 1)) = Some (-4).
  Proof. reflexivity. Qed.
  Example shr_u_neg : u32 (I32.shr_u (i32 (-8)) (i32 1)) = Some 2147483644.
  Proof. reflexivity. Qed.
  Example rotl_wrap : u32 (I32.rotl (i32 (2^31 + 1)) (i32 1)) = Some 3.
  Proof. reflexivity. Qed.
  Example rotr_wrap : u32 (I32.rotr (i32 3) (i32 1)) = Some (2^31 + 1).
  Proof. reflexivity. Qed.

  (* Bit counting *)
  Example clz_one : u32 (I32.clz (i32 1)) = Some 31.
  Proof. reflexivity. Qed.
  Example clz_zero : u32 (I32.clz (i32 0)) = Some 32.
  Proof. reflexivity. Qed.
  Example ctz_eight : u32 (I32.ctz (i32 8)) = Some 3.
  Proof. reflexivity. Qed.
  Example ctz_zero : u32 (I32.ctz (i32 0)) = Some 32.
  Proof. reflexivity. Qed.
  Example popcnt_all : u32 (I32.popcnt (i32 (-1))) = Some 32.
  Proof. reflexivity. Qed.
  Example clz64_one : option_map I64.unsigned (I64.clz (I64.repr 1)) = Some 63.
  Proof. reflexivity. Qed.

  (* Signed vs unsigned comparison *)
  Example lt_s_neg : I32.lt_s (i32 (-1)) (i32 0) = true.
  Proof. reflexivity. Qed.
  Example lt_u_neg : I32.lt_u (i32 (-1)) (i32 0) = false.
  Proof. reflexivity. Qed.

End IntTest.
