(** * Transform Language *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Import imports.

Inductive AbLiteral : Type :=
  | StringLiteral (s : string)
  | Digits (n : nat).

Inductive AbNumExpr : Type :=
  | AbLit (n : nat)
  | AbId (s : string).

Inductive AbBinExpr : Type :=
  | BinTrue
  | BinFalse.

Inductive AbCommand : Type :=
  | AbSkip
  | AbAssign (x : string) (a : AbNumExpr).

Fixpoint AbEval (st : state) (a : AbNumExpr) : nat :=
  match a with
  | AbLit l => l
  | AbId n => st n
  end.

Fixpoint AbBinEval (st : state) (b : AbBinExpr) : bool :=
  match b with
  | BinTrue     => true
  | BinFalse    => false
  end.

Inductive AbExec : AbCommand -> state -> state -> Prop :=
  | Ab_Skip : forall st,
      AbSkip / st \\ st
  | Ab_Assign  : forall st a1 n x,
      AbEval st a1 = n ->
      (AbAssign x a1) / st \\ st & { x --> n }
  where "c1 '/' st '\\' st'" := (AbExec c1 st st').
