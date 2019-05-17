(** * Imports and common features used throughout the program *)
Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Export Coq.Strings.String.
Import ListNotations.

From LF Require Export Maps.

(* Values: These are shared values both programs execute to *)
Inductive prog_value : Type :=
  | pNull
  | pNat (n : nat)
  | pBool (b : bool)
  | pList (v : list nat).

(* Defining the map to hold the state of the program *)
Definition state := total_map prog_value.

Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

(* Method to get a value from a list *)
Fixpoint getValueList (v: list nat) (n : nat) : prog_value :=
  match v with
    | nil => pNull
    | cons h t => match n with
               | 0 => pNat h
               | S n' => getValueList t n'
                 end
  end.

(* Method to unwrap a nat from a prog_value *)
Definition pullOutNat (v : prog_value) : nat :=
  match v with
  | pNat n => n
  | _ => 0
  end.

(* Method to unwrap a bool from a prog_value *)
Definition pullOutBool (v : prog_value) : bool :=
  match v with
  | pBool b => b
  | _ => false
  end.
