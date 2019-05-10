(** * Transform Language *)
(** This file describes the Ab Intio Transform Language.  In this language, everything is
    a transformation.  Ab Initio programs are sequences of transformations.  An example
    Ab Initio program is:
        field1 :: 10
        field2 :: field1 * 4
        field3 :: field1 + field2
    *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Import imports.

(* DECLARATIONS OF AB INITIO TYPES *)

(* Values *)
Inductive AbValue : Type :=
  | AbNat (n : nat)
  | AbBool (b : bool).

(* Values that result in a nat *)
Inductive AbNum : Type :=
  | AbLit (n : nat)
  | AbId (s : string).

(* Numerical expressions *)
Inductive AbNumExpr : Type :=
  | AbNum2 (n : AbNum)
  | AbAdd (a1 : AbNumExpr) (a2 : AbNumExpr)
  | AbSub (a1 : AbNumExpr) (a2 : AbNumExpr)
  | AbMulti (a1 : AbNumExpr) (a2 : AbNumExpr).

(* Values that result in a bool *)
Inductive AbBinExpr : Type :=
  | BinTrue
  | BinFalse
  | AbUnaryOp (b : AbBinExpr)
  | AbLe (a1 : AbNumExpr) (a2 : AbNumExpr)
  | AbEq (a1 : AbNumExpr) (a2 : AbNumExpr)
  | AbNotEq (a1 : AbNumExpr) (a2 : AbNumExpr)
  | AbAnd (b1 : AbBinExpr) (b2 : AbBinExpr)
  | AbOr (b1 : AbBinExpr) (b2 : AbBinExpr).

(* Expressions from the transform language *)
Inductive AbExpr : Type :=
  | Ab_Num_Expr (a : AbNumExpr)
  | Ab_Bin_Expr (b : AbBinExpr).

(* Commands from the transform language *)
Inductive AbCommand : Type :=
  | AbTransform (x : string) (a : AbExpr)
  | AbSeq (c1 c2 : AbCommand).

(* EVALUATIONS OF AB INITIO TYPES *)

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
Fixpoint AbEvalBin (st : state) (b : AbBinExpr) : bool :=
  match b with
  | BinTrue => true
  | BinFalse => false
  | AbUnaryOp b => negb (AbEvalBin st b)
  | AbLe a1 a2 => leb (AbEvalNum st a1) (AbEvalNum st a2)
  | AbEq a1 a2 => Nat.eqb (AbEvalNum st a1) (AbEvalNum st a2)
  | AbNotEq a1 a2 => negb (Nat.eqb (AbEvalNum st a1) (AbEvalNum st a2))
  | AbAnd b1 b2 => andb (AbEvalBin st b1) (AbEvalBin st b2)
  | AbOr b1 b2 => orb (AbEvalBin st b1) (AbEvalBin st b2)
  end.

(* Evaluation of expressions *)
Fixpoint AbEval (st : state) (a : AbExpr) : AbValue :=
  match a with
  | Ab_Num_Expr a => AbNat (AbEvalNum st a)
  | Ab_Bin_Expr b => AbBool (AbEvalBin st b)
  end.

(* OPERATIONAL SEMANTICS OF AB INITIO COMMANDS *)

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
