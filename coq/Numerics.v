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

