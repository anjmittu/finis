(** * Python Language *)
Set Warnings "-notation-overridden,-parsing".
From LF Require Import imports.

Inductive PyLiteral : Type :=
  | StringLiteral (s : string)
  | Digits (n : nat).

Inductive PyNumExpr : Type :=
  | PyLit (n : nat)
  | PyId (s : string).

Inductive PyBinExpr : Type :=
  | PyBinTrue
  | PyBinFalse.

Fixpoint PyEval (st : state) (a : PyNumExpr) : nat :=
  match a with
  | PyLit l => l
  | PyId n => st n
  end.

Fixpoint PyBinEval (st : state) (b : PyBinExpr) : bool :=
  match b with
  | PyBinTrue     => true
  | PyBinFalse    => false
  end.

Inductive PyCommand : Type :=
  | PySkip
  | PyAssign (x : string) (a : PyNumExpr).
