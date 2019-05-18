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

(* Numerical expressions *)
Inductive AbNumExpr : Type :=
  | AbNatLit (n : prog_value) (* Natural number literals *)
  | AbIdNat (s : string) (* ID of a natural number stored in the program state *)
  | AbVectorValue (s : string) (n : nat) (* Natural number stored in a vector *)
  | AbAdd (a1 : AbNumExpr) (a2 : AbNumExpr) (* Adding two natural numbers *)
  | AbSub (a1 : AbNumExpr) (a2 : AbNumExpr) (* Subtracting two natural numbers *)
  | AbMulti (a1 : AbNumExpr) (a2 : AbNumExpr) (* Multiplying two natural numbers *)
  .

(* Values that result in a bool *)
Inductive AbBoolExpr : Type :=
  | BinTrue (* True *)
  | BinFalse (* False *)
  | AbIdBool (s : string) (* ID of a boolean stored in the program state *)
  | AbUnaryOp (b : AbBoolExpr) (* Unary Op on a boolean *)
  | AbLe (a1 : AbNumExpr) (a2 : AbNumExpr) (* Less than op on two natural numbers *)
  | AbEq (a1 : AbNumExpr) (a2 : AbNumExpr) (* Equal op on two natural numbers *)
  | AbNotEq (a1 : AbNumExpr) (a2 : AbNumExpr) (* Not equal op on two natural numbers *)
  | AbAnd (b1 : AbBoolExpr) (b2 : AbBoolExpr) (* And op on two booleans *)
  | AbOr (b1 : AbBoolExpr) (b2 : AbBoolExpr) (* Or op on two booleans *)
  .

(* Expressions from the transform language *)
Inductive AbExpr : Type :=
  | Ab_Num_Expr (a : AbNumExpr)
  | Ab_Bin_Expr (b : AbBoolExpr)
  | Ab_Enc_Expr (e : AbExpr).

(* Commands from the transform language *)
Inductive AbCommand : Type :=
  | AbTransform (x : string) (a : AbExpr)
  | AbSeq (c1 c2 : AbCommand).



(* EVALUATIONS OF AB INITIO TYPES *)

(* Evaluation of numerical expressions *)
Fixpoint AbEvalNum (st : state) (a : AbNumExpr) : prog_value :=
  match a with
  | AbNatLit l => l
  | AbIdNat s => match st s with
                 | pNat n => pNat n
                 | _ => pNull
                 end
  | AbVectorValue s n => match st s with
                            | pList v => getValueList v n
                            | _ => pNull
                            end
  | AbAdd a1 a2 => pNat (pullOutNat (AbEvalNum st a1) + pullOutNat (AbEvalNum st a2))
  | AbSub a1 a2 => pNat (pullOutNat (AbEvalNum st a1) - pullOutNat (AbEvalNum st a2))
  | AbMulti a1 a2 => pNat (pullOutNat (AbEvalNum st a1) * pullOutNat (AbEvalNum st a2))
  end.

(* Evaluation of bool expressions *)
Fixpoint AbEvalBin (st : state) (b : AbBoolExpr) : prog_value :=
  match b with
  | BinTrue => pBool true
  | BinFalse => pBool false
  | AbIdBool s => match st s with
                 | pBool b => pBool b
                 | _ => pNull
                 end
  | AbUnaryOp b => pBool (negb (pullOutBool (AbEvalBin st b)))
  | AbLe a1 a2 => pBool (leb (pullOutNat (AbEvalNum st a1)) (pullOutNat (AbEvalNum st a2)))
  | AbEq a1 a2 => pBool (Nat.eqb (pullOutNat (AbEvalNum st a1)) (pullOutNat (AbEvalNum st a2)))
  | AbNotEq a1 a2 => pBool (negb (Nat.eqb (pullOutNat (AbEvalNum st a1)) (pullOutNat (AbEvalNum st a2))))
  | AbAnd b1 b2 => pBool (andb (pullOutBool (AbEvalBin st b1)) (pullOutBool (AbEvalBin st b2)))
  | AbOr b1 b2 => pBool (orb (pullOutBool (AbEvalBin st b1)) (pullOutBool (AbEvalBin st b2)))
  end.

(* Evaluation of expressions *)
Fixpoint AbEval (st : state) (a : AbExpr) : prog_value :=
  match a with
  | Ab_Num_Expr a => AbEvalNum st a
  | Ab_Bin_Expr b => AbEvalBin st b
  | Ab_Enc_Expr e => AbEval st e
  end.

(* OPERATIONAL SEMANTICS OF AB INITIO COMMANDS *)

(* Execution of commands *)
Inductive AbInitioProgram : AbCommand -> state -> state -> Prop :=
  | Ab_Transform  : forall st a1 n x,
      AbEvalNum st a1 = n ->
      (AbTransform x (Ab_Num_Expr (AbNatLit n))) / st \\ st & { x --> n }
  | Ab_Seq : forall c1 c2 st st' st'',
      c1 / st \\ st' ->
      c2 / st' \\ st'' ->
      (AbSeq c1 c2) / st \\ st''
  where "c1 '/' st '\\' st'" := (AbInitioProgram c1 st st').
