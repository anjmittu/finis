(** * Transform Language *)
Set Warnings "-notation-overridden,-parsing".
From LF Require Import imports.
From LF Require Import transforms.
From LF Require Import python.

Fixpoint numExprCompile (ae : AbNumExpr) : PyNumExpr :=
  match ae with
    | AbLit l => PyLit l
    | AbId n => PyId n
  end.

Fixpoint compile (ac : AbCommand) : PyCommand :=
  match ac with
    | AbSkip => PySkip
    | AbAssign x a => PyAssign x (numExprCompile a)
  end.

Compute compile (AbAssign "x" (AbLit 3)).

Theorem compiler_correctness : forall a st st1 st2,
    (AbExec a st st1) ->
    (PyExec (compile a) st st2) ->
    st1 = st2.
Proof.
  intros.
  induction a; simpl in *; inversion H; inversion H0; subst.
  - reflexivity.
  - induction a; simpl; reflexivity.    
Qed.
