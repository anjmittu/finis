(** * Transform Language *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Import imports.

(* Values that result in a nat *)
Inductive AbNum : Type :=
  | AbLit (n : nat)
  | AbId (s : string).

(* Values that result in a bool *)
Inductive AbBinExpr : Type :=
  | BinTrue
  | BinFalse.

(* Numerical expressions *)
Inductive AbNumExpr : Type :=
  | AbNum2 (n : AbNum)
  | AbAdd (a1 : AbNumExpr) (a2 : AbNumExpr)
  | AbSub (a1 : AbNumExpr) (a2 : AbNumExpr)
  | AbMulti (a1 : AbNumExpr) (a2 : AbNumExpr).

(* Expressions from the transform language *)
Inductive AbExpr : Type :=
  | Ab_Num_Expr (a : AbNumExpr).

(* Commands from the transform language *)
Inductive AbCommand : Type :=
  | AbTransform (x : string) (a : AbExpr)
  | AbSeq (c1 c2 : AbCommand).

(* Evaluation of numerical values *)
Fixpoint AbEvalNumVal (st : state) (a : AbNum) : nat :=
  match a with
  | AbLit l => l
  | AbId n => st n
  end.

(* Evaluation of numerical expressions *)
Fixpoint AbEvalNum (st : state) (a : AbNumExpr) : nat :=
  match a with
  | AbNum2 n => AbEvalNumVal st n
  | AbAdd a1 a2 => (AbEvalNum st a1) + (AbEvalNum st a2)
  | AbSub a1 a2 => (AbEvalNum st a1) - (AbEvalNum st a2)
  | AbMulti a1 a2 => (AbEvalNum st a1) * (AbEvalNum st a2)
  end.

(* Evaluation of bool expressions *)
Fixpoint AbBinEval (st : state) (b : AbBinExpr) : bool :=
  match b with
  | BinTrue => true
  | BinFalse => false
  end.

(* TODO allow bools to be returned *)
(* Evaluation of expressions *)
Fixpoint AbEval (st : state) (a : AbExpr) : nat :=
  match a with
  | Ab_Num_Expr a => AbEvalNum st a
  end.

(* Execution of commands *)
Inductive AbInitioProgram : AbCommand -> state -> state -> Prop :=
  | Ab_Transform  : forall st a1 n x,
      AbEvalNum st a1 = n ->
      (AbTransform x (Ab_Num_Expr (AbNum2 (AbLit n)))) / st \\ st & { x --> n }
  | Ab_Seq : forall c1 c2 st st' st'',
      c1 / st \\ st' ->
      c2 / st' \\ st'' ->
      (AbSeq c1 c2) / st \\ st''
  where "c1 '/' st '\\' st'" := (AbInitioProgram c1 st st').
