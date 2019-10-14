(* ***************************************************************** *)
(* Commons.v                                                         *)
(*                                                                   *)
(* 2019 Xuan Huang                                                   *)
(* ***************************************************************** *)

From Coq Require Export Lists.List.
Export ListNotations.

(* ################################################################# *)
(** * Commons *)

(* ================================================================= *)
(** ** Notations *)

(* ----------------------------------------------------------------- *)
(** *** Epsilon *)
Notation " 'ϵ' " := ([]).

(* ----------------------------------------------------------------- *)
(** *** Indexing *)

Module IndexingNotations.

  Notation idx := nth_error.

  Notation "l '.[' x ]" :=
    (idx l x)
    (at level 60, right associativity) : wasm_scope.

  Open Scope wasm_scope.

  Fixpoint update_idx {A: Type} (l: list A) (n: nat) (x: A) : option (list A) :=
    match l.[n] with
    | None => None
    | Some _ => Some ((firstn n l) ++ [x] ++ (skipn (n+1) l))
    end.

  Module Test.

    Example l := [1;2;3].

    Example i0 : (update_idx l 0 2) = Some [2;2;3].
      auto. Qed.

    Example i1 : (update_idx l 1 4) = Some [1;4;3].
      auto. Qed.

    Example i__overflow : (update_idx l 3 4) = None.
      auto. Qed.

  End Test.

End IndexingNotations.
Export IndexingNotations.



(* ================================================================= *)
(** ** Monads *)

(* ----------------------------------------------------------------- *)
(** *** Monadaic/Fmap option *)

Module OptionMonadNotations.

  Notation "x <- e1 ;; e2" := (match e1 with
                                | Some x => e2
                                | None => None
                                end)
           (right associativity, at level 60) : option_scope.

  Notation " 'return' e "
    := (Some e) (at level 60) : option_scope.

  Notation " 'fail' "
    := None : option_scope.


  Definition fmap_opt {A B: Type} (f: A -> B) (o1: option A) : option B :=
    match o1 with
    | Some x => Some (f x)
    | None => None
    end.

  Notation " f '<$>' o "
    := (fmap_opt f o) (right associativity, at level 60) : option_scope.

  Open Scope option_scope.

  Module Test.

    Example exf :=  (fun i => i + 1) <$> (Some 0).
    Compute exf.

    Example exf__assoc := (fun i => i + 1) <$> (fun i => i + 1) <$> (Some 0).
    Compute exf__assoc.

    Example exm__some :=
      v1 <- Some 1;;
      v2 <- Some 2;;
      return (v1 + v2).
    Compute exm__some.

    Example exm__none :=
      v1 <- Some 1;;
      v2 <- None;;
      return (v1 + v2).
    Compute exm__none.

  End Test.

End OptionMonadNotations.
Export OptionMonadNotations.
