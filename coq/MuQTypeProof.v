Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Permutations.
Require Import QuantumLib.VectorStates.
Require Import Lists.ListSet.
Require Import MuQSyntax.
Require Import MuQSem.
Require Import MuQType.

Local Open Scope nat_scope.

(* This document contains MuQ theorem files. *)

(* We first define the values *)
Definition value (e:exp) :=
  match e with Var x => True
             | Val c => True
             | St s t => True
             | Anni s c t tf => True 
             | Trans (St s t) => True
             | Trans (Anni s c t tf) => True
             | Lambda x t e => True
             | Mu x t e => True
             | _ => False
  end.


(* The type progress theorem. For every well-typed expression, there exists a step. *)
Theorem type_progress: forall g e1 t, typing g e1 t -> value e1 \/ exists e2 e3, equiv e1 e2 /\ sem e2 e3.
Proof.
Admitted.


Theorem type_preservation_1: forall g e1 e2 t, typing g e1 t -> equiv e1 e2 -> exists g', typing g' e2 t.
Proof.
Admitted.


Theorem type_preservation_2: forall g e1 e2 t, typing g e1 t -> sem e1 e2 -> exists g', typing g' e2 t.
Proof.
Admitted.