(** * Transform Language *)
Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Export Coq.Strings.String.
Import ListNotations.

From LF Require Export Maps.

Definition state := total_map nat.

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
