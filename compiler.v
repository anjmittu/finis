
(** * Compiler Logic *)
Set Warnings "-notation-overridden,-parsing".
From LF Require Import imports.
From LF Require Import transforms.
From LF Require Import python.

Fixpoint numCompile (ae : AbNum) : PyNum :=
  match ae with
    | AbLit l => PyLit l
    | AbId n => PyId n
  end.

Fixpoint numExprCompile (ae : AbNumExpr) : PyNumExpr :=
  match ae with
    | AbNum2 n => PyNum2 (numCompile n)
    | AbAdd a1 a2 => PyAdd (numExprCompile a1) (numExprCompile a2)
    | AbSub a1 a2 => PySub (numExprCompile a1) (numExprCompile a2)
    | AbMulti a1 a2 => PyMulti (numExprCompile a1) (numExprCompile a2)
  end.

Fixpoint exprCompile (e : AbExpr) : PyExpr :=
  match e with
    | Ab_Num_Expr n => Py_Num_Expr (numExprCompile n)
  end.

Fixpoint compile (ac : AbCommand) : PyCommand :=
  match ac with
  | AbTransform x a => PyAssign x (exprCompile a)
  | AbSeq c1 c2 => PySeq (compile c1) (compile c2)
  end.

Compute compile (AbTransform "x" (Ab_Num_Expr (AbNum2 (AbLit 3)))).

Theorem numEquiv : forall ab st,
    AbEvalNumVal st ab = PyEvalNumVal st (numCompile ab).
Proof.
  intros; induction ab; reflexivity.
Qed.

Theorem numExprEquiv : forall ab st,
    AbEvalNum st ab = PyEvalNum st (numExprCompile ab).
Proof.
  intros.
  induction ab;
    (* Handles cases for AbAdd, AbSub, AbMulti *)
    try ( induction ab1; induction ab2; simpl in *; rewrite IHab1; rewrite IHab2; reflexivity ).
  - (* AbNum2 -> PyNum2 *)
    induction n; reflexivity.
Qed.

Theorem exprEquiv : forall ab st,
    AbEval st ab = PyEval st (exprCompile ab).
Proof.
  intros. induction ab. apply numExprEquiv.
Qed.

Theorem compiler_correctness : forall a st st1 st2,
    (AbInitioProgram a st st1) ->
    (PythonProgram (compile a) st st2) ->
    st1 = st2.
Proof.
  intros.





  
  induction a.
  - (* AbTransform -> PyAssign *)
    induction a.
    * (* AbNum2 -> PyNum2 *)
      simpl in *.
      
      inversion H; inversion H0; subst. reflexivity.
    * (* AbAdd -> PyAdd *)
      inversion H. inversion H0. subst. .
      apply IHa1.
      + apply H.
  - (* AbSkip -> PyNewLine*) reflexivity.
  - (* AbAssign -> PyAssign *) induction a; simpl; reflexivity.
  - (* AbSeq -> PySeq *) apply IHa1.
    + induction H6.
      * subst. assumption.
      * rewrite IHa2.
Qed.
