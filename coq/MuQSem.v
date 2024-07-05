Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Permutations.
Require Import QuantumLib.VectorStates.
Require Import Lists.ListSet.
Require Import MuQSyntax.

Local Open Scope nat_scope.

(* This document contains the semantics of MuQ, 
    which admits the style of the lambda-calculus substitution based semantics.
   The inductive relation sem take an MuQ exp and outputs another exp. *)

Definition sub_1 (v:nat -> basisket) (j:nat) :=
   fun a => if a =? 0 then (Cmult (sqrt (INR ((snd (v 0%nat)) j))) (fst (v 0)),update (snd (v 0)) j ((snd (v 0) j) -1)) else v a.

Definition add_1 (v:nat -> basisket) (j:nat) :=
   fun a => if a =? 0 then (Cmult (sqrt (INR ((snd (v 0%nat) j) + 1))) (fst (v 0)),update (snd (v 0)) j ((snd (v 0) j) + 1)) else v a.


Definition mut_state (size:nat) (s1 s2: spinbase) :=
   fun i => if i <? size then s1 i else s2 (i-size).

Fixpoint times_state_aux (i:nat) (size:nat) (m:nat) (lsize:nat) (c:C) (v:spinbase) (s:nat -> basisket) (acc:nat -> basisket) :=
  match m with 0 => acc
            | S j => update (times_state_aux i size j lsize c v s acc) (i*size + j) (Cmult c (fst (s j)), mut_state lsize v (snd (s j)))
  end.

Fixpoint times_state (m:nat) (m':nat) (lsize:nat) (s1 s2: nat -> basisket) :=
  match m with 0 => zerostate
           | S j => times_state_aux j m' m' lsize (fst (s1 j)) (snd (s1 j)) s2 (times_state j m' lsize s1 s2)
  end.

Definition put_join (size:nat) (sa sb: parstate) :=
  match sa with Zero => Zero
              | Sup m v =>
    match sb with Zero => Zero
                | Sup m' v' => Sup (m*m') (times_state m m' size v v')
    end
  end.

Definition put_plus (sa sb: parstate) :=
  match sa with Zero => Zero
              | Sup m v =>
    match sb with Zero => Zero
                | Sup m' v' => Sup (m+m') (fun i => if i <? m then v i else v' (i - m))
    end
  end.

Inductive resolve : exp -> nat * parstate -> Prop :=
  | zero_deal : forall t, resolve (St Zero t) (fst t, Zero)
  | st_deal : forall m v t, resolve (St (Sup m v) t) (fst t, Sup m v)
  | tensor_deal: forall ea eb sa sb, resolve ea sa -> resolve eb sb
                 -> resolve (Tensor ea eb) (fst sa + fst sb, put_join (fst sa) (snd sa) (snd sb))
  | resolve_plus: forall ea eb la lb, fst la = fst lb -> resolve ea la -> resolve eb lb
                 -> resolve (Plus ea eb) (fst la, put_plus (snd la) (snd lb)).

Inductive sem : exp -> exp -> Prop :=
  | anni_0 : forall j c t tv v t', (snd (v 0)) j = 0 -> sem (App (Anni j c t tv) (St (Sup 1 v) t')) (St Zero t')
  | anni_n : forall j c t tv v t', (snd (v 0)) j > 0 -> sem (App (Anni j c t tv) (St (Sup 1 v) t')) (St (Sup 1 (sub_1 v j)) t')
  | crea_0 : forall j c t tv v t', (snd (v 0)) j = (snd t) - 1 -> sem (App (Trans (Anni j c t tv)) (St (Sup 1 v) t')) (St Zero t')
  | crea_n : forall j c t tv v t', (snd (v 0)) j < (snd t) - 1 
                 -> sem (App (Trans (Anni j c t tv)) (St (Sup 1 v) t')) (St (Sup 1 (add_1 v j)) t')
  | lambda_rule : forall y t ea eb ,  sem (App (Lambda y t ea) eb) (subst ea y eb)
  | mu_rule : forall y t ea eb ,  sem (App (Lambda y t ea) eb) (subst ea y eb) 
  | inner_rule : forall s s' n m m', sem (App (Trans (St s (n,m))) (St s' (n,m'))) (Val (cal_inner n s s'))
  | nor_rule : forall s n st, resolve s (n,st) -> sem (Nor s) (Nor s).




