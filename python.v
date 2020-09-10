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

(* Numerical expressions *)
Inductive PyNumExpr : Type :=
  | PyNatLit (n : prog_value) (* Natural number literals *)
  | PyIdNat (s : string) (* ID of a natural number stored in the program state *)
  | PyArrayValue (s : string) (n : nat) (* Natural number stored in a vector *)
  | PyAdd (a1 : PyNumExpr) (a2 : PyNumExpr) (* Adding two natural numbers *)
  | PySub (a1 : PyNumExpr) (a2 : PyNumExpr) (* Subtracting two natural numbers *)
  | PyMulti (a1 : PyNumExpr) (a2 : PyNumExpr) (* Multiplying two natural numbers *)
  .

(* Values that result in a bool *)
Inductive PyBoolExpr : Type :=
  | PyBinTrue (* True *)
  | PyBinFalse (* False *)
  | PyIdBool (s : string) (* ID of a boolean stored in the program state *)
  | PyUnaryOp (b : PyBoolExpr) (* Unary Op on a boolean *)
  | PyLe (a1 : PyNumExpr) (a2 : PyNumExpr) (* Less than op on two natural numbers *)
  | PyEq (a1 : PyNumExpr) (a2 : PyNumExpr) (* Equal op on two natural numbers *)
  | PyNotEq (a1 : PyNumExpr) (a2 : PyNumExpr) (* Not equal op on two natural numbers *)
  | PyAnd (b1 : PyBoolExpr) (b2 : PyBoolExpr) (* And op on two booleans *)
  | PyOr (b1 : PyBoolExpr) (b2 : PyBoolExpr) (* Or op on two booleans *)
  .

(* Expressions from the python language *)
Inductive PyExpr : Type :=
  | Py_Num_Expr (a : PyNumExpr)
  | Py_Bin_Expr (b : PyBoolExpr)
  | Py_Enc_Expr (e : PyExpr).

(* Commands from the Python language *)
Inductive PyCommand : Type :=
  | PyAssign (x : string) (a : PyExpr)
  | PyStat (e : PyExpr)
  | PySeq (c1 c2 : PyCommand).




(* EVALUATIONS OF PYTHON TYPES *)

(* Evaluation of numerical expressions *)
Fixpoint PyEvalNum (st : state) (a : PyNumExpr) : prog_value :=
  match a with
  | PyNatLit l => l
  | PyIdNat s => match st s with
              | pNat n => pNat n
              | _ => pNull
              end
  | PyArrayValue s n => match st s with
                         | pList v => getValueList v n
                         | _ => pNull
                         end
  | PyAdd a1 a2 => pNat (pullOutNat (PyEvalNum st a1) + pullOutNat (PyEvalNum st a2))
  | PySub a1 a2 => pNat (pullOutNat (PyEvalNum st a1) - pullOutNat (PyEvalNum st a2))
  | PyMulti a1 a2 => pNat (pullOutNat (PyEvalNum st a1) * pullOutNat (PyEvalNum st a2))
  end.

(* Evaluation of bool expressions *)
Fixpoint PyEvalBin (st : state) (b : PyBoolExpr) : prog_value :=
  match b with
  | PyBinTrue => pBool true
  | PyBinFalse => pBool false
  | PyIdBool s => match st s with
                 | pBool b => pBool b
                 | _ => pNull
                 end
  | PyUnaryOp b => pBool (negb (pullOutBool (PyEvalBin st b)))
  | PyLe a1 a2 => pBool (leb (pullOutNat (PyEvalNum st a1)) (pullOutNat (PyEvalNum st a2)))
  | PyEq a1 a2 => pBool (Nat.eqb (pullOutNat (PyEvalNum st a1)) (pullOutNat (PyEvalNum st a2)))
  | PyNotEq a1 a2 => pBool (negb (Nat.eqb (pullOutNat (PyEvalNum st a1)) (pullOutNat (PyEvalNum st a2))))
  | PyAnd b1 b2 => pBool (andb (pullOutBool (PyEvalBin st b1)) (pullOutBool (PyEvalBin st b2)))
  | PyOr b1 b2 => pBool (orb (pullOutBool (PyEvalBin st b1)) (pullOutBool (PyEvalBin st b2)))
  end.

(* Evaluation of expressions *)
Fixpoint PyEval (st : state) (a : PyExpr) : prog_value :=
  match a with
  | Py_Num_Expr a => PyEvalNum st a
  | Py_Bin_Expr b => PyEvalBin st b
  | Py_Enc_Expr e => PyEval st e
  end.

(* OPERATIONAL SEMANTICS OF PYTHON COMMANDS *)

(* Execution of commands *)
Inductive PythonProgram : PyCommand -> state -> state -> Prop :=
  | Py_Assign  : forall st a1 n x,
      PyEvalNum st a1 = n ->
      (PyAssign x (Py_Num_Expr (PyNatLit n))) / st \\ st & { x --> n }
  | Py_Stat  : forall st a1 n,
      PyEvalNum st a1 = n ->
      (PyStat (Py_Num_Expr (PyNatLit n))) / st \\ st
  | Py_Seq : forall c1 c2 st st' st'',
      c1 / st \\ st' ->
      c2 / st' \\ st'' ->
      (PySeq c1 c2) / st \\ st''
  where "c1 '/' st '\\' st'" := (PythonProgram c1 st st').
