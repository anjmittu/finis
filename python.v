(** * Python Language *)
(** This file describes the relevent portion of the Python Language needed for
    this compiler.  In python, expression can either be evaluated on their own or
    assigned to a variable.  Expressions on their own do not change the state of the program.
    An example Python program is:
        field1 = 10
        4 * 10
        field2 = field1 * 4
        field3 = field1 + field2
        field1 + field3
    *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Import imports.

(* DECLARATIONS OF PYTHON TYPES *)

(* Values that result in a nat *)
Inductive PyNum : Type :=
  | PyLit (n : nat)
  | PyId (s : string).

(* Values that result in a bool *)
Inductive PyBinExpr : Type :=
  | PyBinTrue
  | PyBinFalse.

(* Numerical expressions *)
Inductive PyNumExpr : Type :=
  | PyNum2 (n : PyNum)
  | PyAdd (a1 : PyNumExpr) (a2 : PyNumExpr)
  | PySub (a1 : PyNumExpr) (a2 : PyNumExpr)
  | PyMulti (a1 : PyNumExpr) (a2 : PyNumExpr).

(* Expressions from the python language *)
Inductive PyExpr : Type :=
  | Py_Num_Expr (a : PyNumExpr).

(* Commands from the Python language *)
Inductive PyCommand : Type :=
  | PyAssign (x : string) (a : PyExpr)
  | PyStat (e : PyExpr)
  | PySeq (c1 c2 : PyCommand).

(* EVALUATIONS OF PYTHON TYPES *)

(* Evaluation of numerical values *)
Fixpoint PyEvalNumVal (st : state) (a : PyNum) : nat :=
  match a with
  | PyLit l => l
  | PyId n => st n
  end.

(* Evaluation of numerical expressions *)
Fixpoint PyEvalNum (st : state) (a : PyNumExpr) : nat :=
  match a with
  | PyNum2 n => PyEvalNumVal st n
  | PyAdd a1 a2 => (PyEvalNum st a1) + (PyEvalNum st a2)
  | PySub a1 a2 => (PyEvalNum st a1) - (PyEvalNum st a2)
  | PyMulti a1 a2 => (PyEvalNum st a1) * (PyEvalNum st a2)
  end.

(* Evaluation of bool expressions *)
Fixpoint PyBinEval (st : state) (b : PyBinExpr) : bool :=
  match b with
  | PyBinTrue => true
  | PyBinFalse => false
  end.

(* TODO allow bools to be returned *)
(* Evaluation of expressions *)
Fixpoint PyEval (st : state) (a : PyExpr) : nat :=
  match a with
  | Py_Num_Expr a => PyEvalNum st a
  end.

(* OPERATIONAL SEMANTICS OF PYTHON COMMANDS *)

(* Execution of commands *)
Inductive PythonProgram : PyCommand -> state -> state -> Prop :=
  | Py_Assign  : forall st a1 n x,
      PyEvalNum st a1 = n ->
      (PyAssign x (Py_Num_Expr (PyNum2 (PyLit n)))) / st \\ st & { x --> n }
  | Py_Stat  : forall st a1 n,
      PyEvalNum st a1 = n ->
      (PyStat (Py_Num_Expr (PyNum2 (PyLit n)))) / st \\ st
  | Py_Seq : forall c1 c2 st st' st'',
      c1 / st \\ st' ->
      c2 / st' \\ st'' ->
      (PySeq c1 c2) / st \\ st''
  where "c1 '/' st '\\' st'" := (PythonProgram c1 st st').
