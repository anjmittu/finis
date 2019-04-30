(** * Transform Language *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Import imports.

(* Expressions that result in a nat *)
Inductive AbNum : Type :=
  | AbLit (n : nat)
  | AbId (s : string).

(* Expressions that result in a bool *)
Inductive AbBinExpr : Type :=
  | BinTrue
  | BinFalse.

(* Commands from the transform language *)
Inductive AbCommand : Type :=
  | AbSkip
  | AbAssign (x : string) (a : AbNum)
  | AbAdd (a1 : AbNum) (a2 : AbNum)
  | AbSub (a1 : AbNum) (a2 : AbNum)
  | AbMulti (a1 : AbNum) (a2 : AbNum)
  | AbSeq (c1 : AbCommand) (c2 : AbCommand)
  | AbEnclosed (c1 : AbCommand).

(* Evaluation of numerical expressions *)
Fixpoint AbEval (st : state) (a : AbNum) : nat :=
  match a with
  | AbLit l => l
  | AbId n => st n
  end.

(* Evaluation of bool expressions *)
Fixpoint AbBinEval (st : state) (b : AbBinExpr) : bool :=
  match b with
  | BinTrue => true
  | BinFalse => false
  end.

(* Execution of commands *)
Inductive AbExec : AbCommand -> state -> state -> Prop :=
  | Ab_Skip : forall st,
      AbSkip / st \\ st
  | Ab_Assign  : forall st a1 n x,
      AbEval st a1 = n ->
      (AbAssign x a1) / st \\ st & { x --> n }
  | Ab_Add  : forall st a1 n x,
      AbEval st a1 = n ->
      (AbAdd x a1) / st \\ st & { x --> n }
  | Ab_Seq : forall c1 c2 st st' st'',
      c1 / st \\ st' ->
      c2 / st' \\ st'' ->
      (AbSeq c1 c2) / st \\ st''
  | Ab_Enclosed : forall c1 st st',
      c1 / st \\ st' ->
      (AbEnclosed c1) / st \\ st'
  where "c1 '/' st '\\' st'" := (AbExec c1 st st').
