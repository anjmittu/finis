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

Inductive PyCommand : Type :=
  | PySkip
  | PyAssign (x : string) (a : PyNumExpr).

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

Inductive PyExec : PyCommand -> state -> state -> Prop :=
  | Py_Skip : forall st,
      PySkip / st \\ st
  | Py_Assign  : forall st a1 n x,
      PyEval st a1 = n ->
      (PyAssign x a1) / st \\ st & { x --> n }
  where "c1 '/' st '\\' st'" := (PyExec c1 st st').
