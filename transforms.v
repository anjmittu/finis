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

Inductive AbCommand : Type :=
  | AbSkip
  | AbAssign (x : string) (a : AbNumExpr).
