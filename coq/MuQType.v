Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Permutations.
Require Import QuantumLib.VectorStates.
Require Import Lists.ListSet.
Require Import MuQSyntax.

Local Open Scope nat_scope.

(* This document contains the type system of MuQ, based on the simple typed lambda calculus type system.
   The typing relation takes in the equivalence relation to switch different kinds of matrices.
   There are three kinds of mtrices: P, H, and U. P refers to a single creator/annihilator operation,
   H refers to a Hermitian matrix where its transpose is the same as the matrix.
   U is the unitary, taking the exponent of the Hermitian matrix. *)

Fixpoint check_base_aux (n:nat) (s:spinbase) (i:nat) (m:nat) :=
   match n with 0 => True
              | S j => check_base_aux j s i m /\ (s i j) < m
   end.

Fixpoint check_base (s:spinbase) (nl:list partype) :=
   match nl with [] => True
              | ((n,m)::ml) => check_base_aux n s (length ml) m /\ check_base s ml
   end.

Fixpoint good_base' (m:nat) (v:nat -> basisket) (nl: list partype) :=
  match m with 0 => True
            | S j => good_base' j v nl /\ check_base (snd (v j)) nl
  end.

Definition good_base (s:parstate) (nl:list partype) := 
  match s with Zero => True
             | Sup m v => good_base' m v nl
  end.

Inductive merge : type -> type -> type -> Prop :=
  | merge_st: forall s1 s2, merge (TType s1) (TType s2) (TType (TenType s1 s2))
  | merge_dot: forall s1 s2, merge (IType s1) (IType s2) (IType (TenType s1 s2))
  | merge_fun: forall f s1 s2, merge (FType f s1) (FType f s2) (FType f (TenType s1 s2)).

Inductive join : typeflag -> typeflag -> typeflag -> Prop :=
  | join_same : forall tf, join tf tf tf
  | join_p1 : forall tf, join P tf P
  | join_p2 : forall tf, join tf P P.

Fixpoint toTensor (l:list partype) :=
  match l with [] => None
             | a::ml => match toTensor (ml) with None => Some (SType a) | Some t => Some (TenType (SType a) t) end
  end.

Inductive typing : (var -> type) -> exp -> type -> Prop :=
  | tpar : forall g t e1 e2, equiv e1 e2 -> typing g e2 t -> typing g e1 t
  | tvar : forall g x, typing g (Var x) (g x)
  | tval : forall g c, typing g (Val c) CT
  | tvec : forall g s t t', good_base s t -> toTensor t = Some t' -> typing g (St s t) t'
  | top : forall g j c t tf, j < fst t -> typing g (Anni j c t tf) (FType tf (SType t))
  | tlambda: forall g y t ea t', typing (update g y t) ea t' -> typing g (Lambda y t ea) t'
  | tmu : forall g y t ea, typing (update g y (FTy t t)) ea t -> typing g (Mu y t ea) (FTy t t)
  | tdag : forall g e t, typing g e (TType t) -> typing g (Trans e) (IType t)
  | ttrans: forall g e tf t, typing g e (FType tf t) -> typing g (Trans e) (FType tf t)
  | ttensor: forall g e1 e2 t1 t2 t3, typing g e1 t1 -> typing g e2 t2 -> merge t1 t2 t3 -> typing g (Tensor e1 e2) t3
  | tplus: forall g e1 e2 t, typing g e1 t -> typing g e2 t -> typing g (Plus e1 e2) t
  | tapp: forall g e1 e2 t1 t2, typing g e1 (FTy t1 t2) -> typing g e2 t1 -> typing g (App e1 e2) t2
  | tmat: forall g e1 e2 tf t, typing g e1 (FType tf t) -> typing g e2 (TType t) -> typing g (App e1 e2) (TType t)
  | tinner: forall g e1 e2 t, typing g e1 (IType t) -> typing g e2 (TType t) -> typing g (App e1 e2) CT
  | tseq: forall g e1 e2 tf1 tf2 tf3 t, typing g e1 (FType tf1 t) -> typing g e2 (FType tf2 t) 
                                -> join tf1 tf2 tf3 -> typing g (App e1 e2) (FType tf3 t)
  | tnor1: forall g e t, typing g e (TType t) -> typing g (Nor e) (TType t)
  | tnor2: forall g e t, typing g e (IType t) -> typing g (Nor e) (IType t)
  | ther : forall g e t, typing g e (FType P t) -> equiv (Trans e) e -> typing g e (FType H t)
  | texp : forall g e t, typing g e (FType H t) -> typing g (Exp e) (FType U t)
  | tlog : forall g e t, typing g e (FType U t) -> typing g (Log e) (FType H t).




