(** * Transform Language *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Import imports.

(* Expressions that result in a nat *)
Inductive AbNumExpr : Type :=
  | AbLit (n : nat)
  | AbId (s : string).

(* Expressions that result in a bool *)
Inductive AbBinExpr : Type :=
  | BinTrue
  | BinFalse.

(* Commands from the transform language *)
Inductive AbCommand : Type :=
  | AbSkip
  | AbAssign (x : string) (a : AbNumExpr).

(* Evaluation of numerical expressions *)
Fixpoint AbEval (st : state) (a : AbNumExpr) : nat :=
  match a with
  | AbLit l => l
  | AbId n => st n
  end.

(* Evaluation of bool expressions *)
Fixpoint AbBinEval (st : state) (b : AbBinExpr) : bool :=
  match b with
  | BinTrue => true
  | BinFalse => false
  end.

(* Execution of commands *)
Inductive AbExec : AbCommand -> state -> state -> Prop :=
  | Ab_Skip : forall st,
      AbSkip / st \\ st
  | Ab_Assign  : forall st a1 n x,
      AbEval st a1 = n ->
      (AbAssign x a1) / st \\ st & { x --> n }
  where "c1 '/' st '\\' st'" := (AbExec c1 st st').
