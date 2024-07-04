Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Permutations.
Require Import QuantumLib.VectorStates.
(*
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat Permutation. 
Require Import Dirac.
Require Import QPE.
Require Import OQASM.
Require Import BasicUtility.
Require Import Classical_Prop.
Require Import MathSpec.
Require Import QafnySyntax.
(**********************)
(** Locus Definitions **)
(**********************)

Require Import ListSet.
Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
*)
Local Open Scope nat_scope.

Definition var := nat.

Definition spinbase : Type := (nat -> nat).

Definition basisket : Type := C * spinbase.

Inductive parstate : Type := Sup (m:nat) (s:nat -> basisket) | Zero.

Definition sigma : Set := nat.

Definition partype :Set := nat * nat.

Inductive qtype : Set := SType (p:partype) | TenType (l:qtype) (r:qtype).

Coercion SType : partype >-> qtype.

Inductive typeflag : Set := P | U | H. 

Inductive ttype : Set := TType (q:qtype) | IType (q:qtype) | FType (tv:typeflag) (q:qtype).

Coercion TType : qtype >-> ttype.

Inductive type : Set := CT | QTy (t:ttype) | FTy (t1:type) (t2:type).

Coercion QTy : ttype >-> type.

Inductive exp := 
        | Var (x:var)
        | St (s:parstate) (t:partype)
        | Anni (s:sigma) (c:C) (t:partype) (tf:typeflag)
        | Trans (e:exp)
        | Tensor (e1:exp) (e2:exp)
        | Plus (e1:exp) (e2:exp)
        | Nor (e:exp)
        | Exp (e:exp)
        | Log (e:exp)
        | Lambda (x:var) (t:type) (e:exp)
        | Mu (x:var) (t:type) (e:exp)
        | If (e1:exp) (e2:exp) (e3:exp)
        | App (e1:exp) (e2:exp).


Definition anti_s (s:state) (t:type) :=
   match s with Zero => Zero
             | Pair n1 n2 => Pair (t-n1) (t-n2)
   end.

Inductive sem : exp -> exp -> Prop :=
    anni_0 : forall s n, sem (App (Anni s) (St Zero n)) (St Zero n)
  | anni_bot_l : forall n t, sem (App (Anni Up) (St (Pair 0 n) t)) (St Zero t)
  | anni_bot_r : forall n t, sem (App (Anni Down) (St (Pair n 0) t)) (St Zero t)
  | anni_l : forall n1 n2 t, 0 < n1 -> sem (App (Anni Up) (St (Pair n1 n2) t)) (St (Pair (n1-1) n2) t)
  | anni_r : forall n1 n2 t, 0 < n2 -> sem (App (Anni Down) (St (Pair n1 n2) t)) (St (Pair n1 (n2-1)) t)
  | trans_app: forall e s s' t, sem (App e (St (anti_s s t) t)) (St s' t) 
                           -> sem (App (Trans e) (St s t)) (St (anti_s s' t) t)
  | tensor_app: forall e1 e2 e3 e4, sem (App (Tensor e1 e2) (Tensor e3 e4)) (Tensor (App e1 e3) (App e2 e4)).







