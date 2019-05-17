
(** * Compiler Logic *)
Set Warnings "-notation-overridden,-parsing".
From LF Require Import imports.
From LF Require Import transforms.
From LF Require Import python.

Fixpoint numExprCompile (ae : AbNumExpr) : PyNumExpr :=
  match ae with
    | AbNatLit l => PyNatLit l
    | AbIdNat n => PyIdNat n
    | AbVectorValue s n => PyArrayValue s n
    | AbAdd a1 a2 => PyAdd (numExprCompile a1) (numExprCompile a2)
    | AbSub a1 a2 => PySub (numExprCompile a1) (numExprCompile a2)
    | AbMulti a1 a2 => PyMulti (numExprCompile a1) (numExprCompile a2)
  end.

Fixpoint binExprCompile (b : AbBinExpr) : PyBinExpr :=
  match b with
  | BinTrue => PyBinTrue
  | BinFalse => PyBinFalse
  | AbIdBool s => PyIdBool s
  | AbUnaryOp b => PyUnaryOp (binExprCompile b)
  | AbLe a1 a2 => PyLe (numExprCompile a1) (numExprCompile a2)
  | AbEq a1 a2 => PyEq (numExprCompile a1) (numExprCompile a2)
  | AbNotEq a1 a2 => PyNotEq (numExprCompile a1) (numExprCompile a2)
  | AbAnd b1 b2 => PyAnd (binExprCompile b1) (binExprCompile b2)
  | AbOr b1 b2 => PyOr (binExprCompile b1) (binExprCompile b2)
  end.

Fixpoint exprCompile (e : AbExpr) : PyExpr :=
  match e with
  | Ab_Num_Expr n => Py_Num_Expr (numExprCompile n)
  | Ab_Bin_Expr b => Py_Bin_Expr (binExprCompile b)
  end.

Fixpoint compile (ac : AbCommand) : PyCommand :=
  match ac with
  | AbTransform x a => PyAssign x (exprCompile a)
  | AbSeq c1 c2 => PySeq (compile c1) (compile c2)
  end.

Compute compile (AbTransform "x" (Ab_Num_Expr (AbNatLit (pNat 3)))).

Theorem numExprEquiv : forall ab st,
    AbEvalNum st ab = PyEvalNum st (numExprCompile ab).
Proof.
  intros.
  induction ab; simpl;
    (* Solves cases: AbIdNat -> PyIdNat, AbArrayValue -> PyArrayValue *)
    try destruct (st s);
    (* Solves cases: AbAdd -> PyAdd, AbSub -> PySub, AbMulti -> PyMulti *)
    try (rewrite IHab1;  rewrite IHab2);
    (* Solves cases: AbNatLit -> PyNatLit *)
    try reflexivity.
Qed.

Theorem binExprEquiv : forall ab st,
    AbEvalBin st ab = PyEvalBin st (binExprCompile ab).
Proof.
  intros.
  induction ab; simpl in *; try rewrite IHab; try reflexivity.
  - (* AbLe -> PyLe *)
    rewrite numExprEquiv. rewrite numExprEquiv. reflexivity.
  - (* AbEq -> PyEq *)
    rewrite numExprEquiv. rewrite numExprEquiv. reflexivity.
  - (* AbNotEq -> PyNotEq *)
    rewrite numExprEquiv. rewrite numExprEquiv. reflexivity.
  - (* AbAnd -> PyAnd *)
    rewrite IHab1. rewrite IHab2. reflexivity.
  - (* AbOr -> PyOr *)
    rewrite IHab1. rewrite IHab2. reflexivity.
Qed.

Theorem exprEquiv : forall ab st,
    AbEval st ab = PyEval st (exprCompile ab).
Proof.
  intros. induction ab; simpl in *; try rewrite numExprEquiv; try rewrite binExprEquiv; reflexivity.
Qed.

Theorem compiler_correctness : forall a st st1 st2,
    (AbInitioProgram a st st1) ->
    (PythonProgram (compile a) st st2) ->
    st1 = st2.
Proof.
  induction a.
  - (* AbTransform -> PyAssign *)
    induction a.
    + (* Ab_Num_Expr -> Py_Num_Expr *)
      induction a; intros; try inversion H.
      (* AbNumLit -> PyNumLit *)
      induction n; simpl in *; inversion H0; subst; reflexivity.
    + (* Ab_Bin_Expr -> Py_Bin_Expr *)
      induction b; intros; inversion H.
  - (* AbSeq -> PySeq *)
    intros st st'1 st'2 H1 H2.
    inversion H1. inversion H2.
    subst.
    rewrite IHa2 with (st := st') (st1 := st'1) (st2 := st'2).
    reflexivity.
    assumption.
    rewrite IHa1 with (st := st) (st1 := st') (st2 := st'0); assumption.
Qed.
