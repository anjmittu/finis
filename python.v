(** * Python Language *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Import imports.

(* Expressions that result in a nat *)
Inductive PyNumExpr : Type :=
  | PyLit (n : nat)
  | PyId (s : string).

(* Expressions that result in a bool *)
Inductive PyBinExpr : Type :=
  | PyBinTrue
  | PyBinFalse.

(* Commands from the python language *)
Inductive PyCommand : Type :=
  | PyNewLine
  | PyAssign (x : string) (a : PyNumExpr)
  | PySeq (c1 : PyCommand) (c2 : PyCommand).

(* Evaluation of numerical expressions *)
Fixpoint PyEval (st : state) (a : PyNumExpr) : nat :=
  match a with
  | PyLit l => l
  | PyId n => st n
  end.

(* Evaluation of bool expressions *)
Fixpoint PyBinEval (st : state) (b : PyBinExpr) : bool :=
  match b with
  | PyBinTrue => true
  | PyBinFalse => false
  end.

(* Execution of commands *)
Inductive PyExec : PyCommand -> state -> state -> Prop :=
  | Py_NewLine : forall st,
      PyNewLine / st \\ st
  | Py_Assign  : forall st a1 n x,
      PyEval st a1 = n ->
      (PyAssign x a1) / st \\ st & { x --> n }
  | Py_Seq : forall c1 c2 st st' st'',
      c1 / st \\ st' ->
      c2 / st' \\ st'' ->
      (PySeq c1 c2) / st \\ st''
  where "c1 '/' st '\\' st'" := (PyExec c1 st st').
