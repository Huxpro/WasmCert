(* ***************************************************************** *)
(* Numerics.v                                                        *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)


(* ################################################################# *)
(** * Numerics *)

From Wasm Require Export Values.
From Wasm Require Export Structure.
Import OptionMonadNotations.

Module S := Structure.

(* ================================================================= *)
(** * Runtime Type Error (Stuck) *)

Inductive runtime_err (X:Type) : Type :=
  | Ok (x : X)
  | Err.

Arguments Ok {X} _.
Arguments Err {X}.



(* ================================================================= *)
(** * Int Operator *)

(* took me a while to find the syntax of module shared constraints: 
   https://coq.inria.fr/refman/language/gallina-extensions.html#module-system
 *)

Module IntOp (IXX : Int.S) (Val : ValType with Definition t := IXX.t). 

  Import S.IntOp.

  Definition to_val := Val.to_val.
  Definition of_val := Val.of_val.

  Definition unop op : (val -> runtime_err (option val)) :=
    let f :=
      match op with
      | Clz => IXX.clz
      | Ctz => IXX.ctz
      | Popcnt => IXX.popcnt
      end
    in
    fun (v : val) =>
      match of_val v with
      | Some i1 => Ok (to_val <$> f i1)
      | None => Err
      end.


  Definition binop op : (val -> val -> runtime_err (option val)) :=
    let f :=
      match op with
      | Add => IXX.add
      | Sub => IXX.sub
      | Mul => IXX.mul
      | Div sx =>
        match sx with
        | U => IXX.div_u
        | S => IXX.div_s
        end
      | Rem sx =>
        match sx with
        | U => IXX.rem_u
        | S => IXX.rem_s
        end
      | And => IXX.and
      | Or => IXX.or
      | Xor => IXX.xor
      | Shl => IXX.shl
      | Shr sx =>
        match sx with
        | U => IXX.shr_u
        | S => IXX.shr_s
        end
      | Rotl => IXX.rotl
      | Rotr => IXX.rotr
      end
    in
    fun (v1 v2 : val) =>
      match of_val v1, of_val v2 with
      | Some i1, Some i2 => Ok (to_val <$> f i1 i2)
      | _, _ => Err
      end.


  Definition testop op : (val -> runtime_err bool) :=
    let f :=
      match op with
      | Eqz => IXX.eqz
      end
    in
    fun (v : val) =>
      match of_val v with
      | Some i => Ok (f i)
      | None => Err
      end.
      

  Definition relop op : (val -> val -> runtime_err bool) :=
    let f :=
      match op with
      | Eq => IXX.eq
      | Ne => IXX.ne
      | Lt sx =>
        match sx with
        | U => IXX.lt_s
        | S => IXX.lt_u
        end
      | Le sx =>
        match sx with
        | U => IXX.le_s
        | S => IXX.le_u
        end
      | Gt sx =>
        match sx with
        | U => IXX.gt_s
        | S => IXX.gt_u
        end
      | Ge sx =>
        match sx with
        | U => IXX.ge_s
        | S => IXX.ge_u
        end
      end
    in
    fun (v1 v2 : val) =>
      match of_val v1, of_val v2 with
      | Some i1, Some i2 => Ok (f i1 i2)
      | _, _ => Err
      end.

End IntOp. 

Module IOp32 := IntOp (I32) (IVal32).
Module IOp64 := IntOp (I64) (IVal64).



(* ================================================================= *)
(** * Float Operator *)


Module FloatOp (FXX : Float.S) (Val : ValType with Definition t := FXX.t). 

  Import S.FloatOp.

  Definition to_val := Val.to_val.
  Definition of_val := Val.of_val.

  Definition unop op : (val -> runtime_err (option val)) :=
    let f :=
      match op with
      | Neg => FXX.neg
      | Abs => FXX.abs
      | Sqrt => FXX.sqrt
      | Ceil => FXX.ceil
      | Floor => FXX.floor
      | Trunc => FXX.trunc
      | Nearest => FXX.nearest
      end
    in
    fun (v : val) =>
      match of_val v with
      | Some f1 => Ok (to_val <$> f f1)
      | None => Err
      end.
      

  Definition binop op : (val -> val -> runtime_err (option val)) :=
    let f :=
      match op with
      | Add => FXX.add
      | Sub => FXX.sub
      | Mul => FXX.mul
      | Div => FXX.div
      | Min => FXX.min
      | Max => FXX.max
      | Copysign => FXX.copysign
      end
    in
    fun (v1 v2 : val) =>
      match of_val v1, of_val v2 with
      | Some f1, Some f2 => Ok (to_val <$> f f1 f2)
      | _, _ => Err
      end.
  

  Definition testop (op : testop) : (val -> runtime_err bool) :=
    fun v => Err.
      

  Definition relop op : (val -> val -> runtime_err bool) :=
    let f :=
      match op with
      | Eq => FXX.eq
      | Ne => FXX.ne
      | Lt => FXX.lt
      | Le => FXX.le
      | Gt => FXX.gt
      | Ge => FXX.ge
      end
    in
    fun (v1 v2 : val) =>
      match of_val v1, of_val v2 with
      | Some f1, Some f2 => Ok (f f1 f2)
      | _, _ => Err
      end.

End FloatOp. 

Module FOp32 := FloatOp (F32) (FVal32).
Module FOp64 := FloatOp (F64) (FVal64).


(** Dispatch *)

Definition eval_unop (ops: @op S.IntOp.unop S.IntOp.unop S.FloatOp.unop S.FloatOp.unop) := 
  match ops with
  | i32 x => IOp32.unop x
  | i64 x => IOp64.unop x
  | f32 x => FOp32.unop x
  | f64 x => FOp64.unop x
  end.


Definition eval_binop (ops: @op S.IntOp.binop S.IntOp.binop S.FloatOp.binop S.FloatOp.binop) :=
  match ops with
  | i32 x => IOp32.binop x
  | i64 x => IOp64.binop x
  | f32 x => FOp32.binop x
  | f64 x => FOp64.binop x
  end.

Definition eval_testop (ops: @op S.IntOp.testop S.IntOp.testop S.FloatOp.testop S.FloatOp.testop) :=
  match ops with
  | i32 x => IOp32.testop x
  | i64 x => IOp64.testop x
  | f32 x => FOp32.testop x
  | f64 x => FOp64.testop x
  end.

Definition eval_relop (ops: @op S.IntOp.relop S.IntOp.relop S.FloatOp.relop S.FloatOp.relop) :=
  match ops with
  | i32 x => IOp32.relop x
  | i64 x => IOp64.relop x
  | f32 x => FOp32.relop x
  | f64 x => FOp64.relop x
  end.

(* post pone convertion op

Definition eval_cvtop (ops: @op S.IntOp.cvtop S.IntOp.cvtop S.FloatOp.cvtop S.FloatOp.cvtop) :=
  match ops with
  | i32 x => IOp32.cvtop x
  | i64 x => IOp64.cvtop x
  | f32 x => FOp32.cvtop x
  | f64 x => FOp64.cvtop x
  end.

*)


(*  not sure how to write the generic function...

Definition eval_op iop32 iop64 fop32 fop64 :=
  fun {i32 i64 f32 f64 : Type} (ops : op i32 i64 f32 f64) =>
  match ops with
  | i32 x => iop32 x
  | i64 x => iop64 x
  | f32 x => fop32 x
  | f64 x => fop64 x
  end. 

Definition eval_unop := eval_op S.IntOp.unop S.IntOp.unop S.FloatOp.unop S.FloatOp.unop.

*)


Section NumericsPreservation.

Lemma eval_unop_preserve_type : forall op val1 val,
    eval_unop op val1 = Ok (Some val) ->
    type_of op = type_of val.
Proof.
  intros.
  unfold eval_unop in *.
  destruct op; destruct val1; destruct val; simpl in *;
    (* good cases *)
    try reflexivity;

    (* bad cases *)
    inverts H; unfold OptionMonadNotations.fmap_opt in *;
      destruct u;
      try (try (destruct (I32.clz t); inverts H1; inverts H1);
           try (destruct (I32.ctz t); inverts H1; inverts H1);
           try (destruct (I32.popcnt t); inverts H1; inverts H1)
          );
      try (try (destruct (I64.clz t); inverts H1; inverts H1);
           try (destruct (I64.ctz t); inverts H1; inverts H1);
           try (destruct (I64.popcnt t); inverts H1; inverts H1)
          );
      try (try (destruct (F32.neg t); inverts H1; inverts H1);
           try (destruct (F32.abs t); inverts H1; inverts H1);
           try (destruct (F32.sqrt t); inverts H1; inverts H1);
           try (destruct (F32.ceil t); inverts H1; inverts H1);
           try (destruct (F32.floor t); inverts H1; inverts H1);
           try (destruct (F32.trunc t); inverts H1; inverts H1);
           try (destruct (F32.nearest t); inverts H1; inverts H1)
          );
      try (try (destruct (F64.neg t); inverts H1; inverts H1);
           try (destruct (F64.abs t); inverts H1; inverts H1);
           try (destruct (F64.sqrt t); inverts H1; inverts H1);
           try (destruct (F64.ceil t); inverts H1; inverts H1);
           try (destruct (F64.floor t); inverts H1; inverts H1);
           try (destruct (F64.trunc t); inverts H1; inverts H1);
           try (destruct (F64.nearest t); inverts H1; inverts H1)
          ).
Qed.

Lemma eval_binop_preserve_type : forall op val1 val2 val,
    eval_binop op val1 val2 = Ok (Some val) ->
    type_of op = type_of val.
Proof.
  intros.
  unfold eval_binop in *.
  destruct op; destruct val1; destruct val2; destruct val; simpl in *;
    (* good cases *)
    try reflexivity;

    (* bad cases *)
    inverts H; unfold OptionMonadNotations.fmap_opt in *;
      destruct b;
      try (destruct s); 
      try (try (destruct (I32.add t t0); inverts H1; inverts H1);
           try (destruct (I32.sub t t0); inverts H1; inverts H1);
           try (destruct (I32.mul t t0); inverts H1; inverts H1);
           try (destruct (I32.and t t0); inverts H1; inverts H1);
           try (destruct (I32.or t t0); inverts H1; inverts H1);
           try (destruct (I32.xor t t0); inverts H1; inverts H1);
           try (destruct (I32.shl t t0); inverts H1; inverts H1);
           try (destruct (I32.rotl t t0); inverts H1; inverts H1);
           try (destruct (I32.rotr t t0); inverts H1; inverts H1);
           try (destruct (I32.div_u t t0); inverts H1; inverts H1);
           try (destruct (I32.div_s t t0); inverts H1; inverts H1);
           try (destruct (I32.rem_u t t0); inverts H1; inverts H1);
           try (destruct (I32.rem_s t t0); inverts H1; inverts H1);
           try (destruct (I32.shr_u t t0); inverts H1; inverts H1);
           try (destruct (I32.shr_s t t0); inverts H1; inverts H1)
          );
      try (try (destruct (I64.add t t0); inverts H1; inverts H1);
           try (destruct (I64.sub t t0); inverts H1; inverts H1);
           try (destruct (I64.mul t t0); inverts H1; inverts H1);
           try (destruct (I64.and t t0); inverts H1; inverts H1);
           try (destruct (I64.or t t0); inverts H1; inverts H1);
           try (destruct (I64.xor t t0); inverts H1; inverts H1);
           try (destruct (I64.shl t t0); inverts H1; inverts H1);
           try (destruct (I64.rotl t t0); inverts H1; inverts H1);
           try (destruct (I64.rotr t t0); inverts H1; inverts H1);
           try (destruct (I64.div_u t t0); inverts H1; inverts H1);
           try (destruct (I64.div_s t t0); inverts H1; inverts H1);
           try (destruct (I64.rem_u t t0); inverts H1; inverts H1);
           try (destruct (I64.rem_s t t0); inverts H1; inverts H1);
           try (destruct (I64.shr_u t t0); inverts H1; inverts H1);
           try (destruct (I64.shr_s t t0); inverts H1; inverts H1)
          );
      try (try (destruct (F32.add t t0); inverts H1; inverts H1);
           try (destruct (F32.sub t t0); inverts H1; inverts H1);
           try (destruct (F32.mul t t0); inverts H1; inverts H1);
           try (destruct (F32.div t t0); inverts H1; inverts H1);
           try (destruct (F32.min t t0); inverts H1; inverts H1);
           try (destruct (F32.max t t0); inverts H1; inverts H1);
           try (destruct (F32.copysign t t0); inverts H1; inverts H1)
          );
      try (try (destruct (F64.add t t0); inverts H1; inverts H1);
           try (destruct (F64.sub t t0); inverts H1; inverts H1);
           try (destruct (F64.mul t t0); inverts H1; inverts H1);
           try (destruct (F64.div t t0); inverts H1; inverts H1);
           try (destruct (F64.min t t0); inverts H1; inverts H1);
           try (destruct (F64.max t t0); inverts H1; inverts H1);
           try (destruct (F64.copysign t t0); inverts H1; inverts H1)
          ).
Qed.



(* ----------------------------------------------------------------- *)
(** *** Archive *)

(* These two conclusion is wrong...
   During the [preservation] proof we only need to simpl [type_of b = T_i32] which is obvious.

   Archived the structure for possible uses in variant form.
 *)
Lemma eval_testop_preserve_type : forall op val1 (b: bool),
    eval_testop op val1 = Ok b ->
    type_of op = type_of (b: val).
Proof.
  intros.
  unfold eval_testop in *.
  destruct op; destruct val1; simpl in *; (* [type_of b = T_i32] *)
    (* good cases *)
    try reflexivity;

    (* bad cases *)
    try solve [inverts H; destruct t; simpl].

  - (*
        IOp64.testop S.IntOp.Eqz (i64 t0) = Ok b
        ----------------------------------------
                 T_i64 = T_i32
     *)
    destruct t.
    destruct IOp64.testop.
    + admit.
    + inverts H.
Admitted.

Lemma eval_relop_preserve_type : forall op val1 val2 (b: bool),
    eval_relop op val1 val2 = Ok b ->
    type_of op = type_of (b: val).
Proof.
  intros.
  unfold eval_relop in *.
  destruct op; destruct val1; destruct val2; simpl in *; (* [type_of b = T_i32] *)
    (* good cases *)
    try reflexivity;

    (* bad cases *)
    try solve [inverts H; destruct t; simpl].

    - admit. (* We need a way to re-interpret bool -> i32 -> i64? *)
    - admit. (* We need a way to re-interpret bool -> i32 -> f32? *)
    - admit. (* We need a way to re-interpret bool -> i32 -> f64? *)
Admitted.

End NumericsPreservation.