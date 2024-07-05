Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.

Local Open Scope nat_scope.

(* This document contains the syntax of MuQ, which is an extension of Lambda/mu calculus with second quantization.
   The inductive relation equiv defines the expression equivalence relations.
 *)

Definition var := nat.

Definition spinbase : Type := (nat -> nat).

Definition allzero := fun (_:nat) => 0.

Definition basisket : Type := C * spinbase.

Definition zerostate := fun (_:nat) => (C0, allzero).

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
        | Val (c:C)
        | Mul (c:C) (e:exp)
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


Fixpoint subst (e:exp) (x:var) (e1:exp) :=
  match e with Var y => if x =? y then e1 else Var y
             | Val c => Val c
             | St s t => St s t
             | Mul c ea => Mul c (subst ea x e1)
             | Anni s c t tf => Anni s c t tf
             | Trans ea => Trans (subst ea x e1)
             | Tensor ea eb => Tensor (subst ea x e1) (subst eb x e1)
             | Plus ea eb => Plus (subst ea x e1) (subst eb x e1)
             | Nor ea => Nor (subst ea x e1)
             | Exp ea => Exp (subst ea x e1)
             | Log ea => Log (subst ea x e1)
             | Lambda y t ea => if x =? y then Lambda y t ea else Lambda y t (subst ea x e1)
             | Mu y t ea => if x =? y then Mu y t ea else Mu y t (subst ea x e1)
             | If ea eb ec => If (subst ea x e1) (subst eb x e1) (subst ec x e1)
             | App ea eb => App (subst ea x e1) (subst eb x e1)
  end.

Fixpoint list_sub (s:list var) (b:var) :=
   match s with nil => nil
              | a::al => if a =? b then list_sub al b else a::list_sub al b
   end.

Fixpoint freeVars (e:exp) :=
  match e with Var y => [y]
             | Val c => []
             | St s t => []
             | Anni s c t tf => []
             | Mul c ea => freeVars ea
             | Trans ea => freeVars ea
             | Tensor ea eb => freeVars ea ++ freeVars eb
             | Plus ea eb =>freeVars ea ++ freeVars eb
             | Nor ea => freeVars ea
             | Exp ea => freeVars ea
             | Log ea => freeVars ea
             | Lambda y t ea => list_sub (freeVars ea) y
             | Mu y t ea => list_sub (freeVars ea) y
             | If ea eb ec => freeVars ea ++ freeVars eb ++ freeVars ec
             | App ea eb => freeVars ea ++ freeVars eb
  end.

Fixpoint varCap (e:exp) (x:var) :=
  match e with Var y => False
             | Val c => False
             | St s t => False
             | Anni s c t tf => False
             | Mul c ea => varCap ea x
             | Trans ea => varCap ea x 
             | Tensor ea eb => varCap ea x \/ varCap eb x 
             | Plus ea eb => varCap ea x \/ varCap eb x 
             | Nor ea => varCap ea x 
             | Exp ea => varCap ea x 
             | Log ea => varCap ea x 
             | Lambda y t ea => if x =? y then True else varCap ea x 
             | Mu y t ea => if x =? y then True else varCap ea x 
             | If ea eb ec => varCap ea x \/ varCap eb x \/ varCap ec x
             | App ea eb => varCap ea x \/ varCap eb x 
  end.

Fixpoint cal_dot (s1 s2:spinbase) (n:nat) :=
  match n with 0 => true
             | S m => if s1 m =? s2 m then cal_dot s1 s2 m else false
  end.

Fixpoint cal_inner_aux' (m:nat) (n:nat) (s2:basisket) (s1:nat -> basisket) :=
   match m with 0 => C0
              | S j =>  if cal_dot (snd s2) (snd (s1 j)) n
                        then Cplus (Cmult (fst s2) (fst (s1 j))) (cal_inner_aux' j n s2 s1)
                        else cal_inner_aux' j n s2 s1
   end.
Definition cal_inner_aux (n:nat) (s2:basisket) (s1:parstate) :=
   match s1 with Sup m p => cal_inner_aux' m n s2 p | Zero => C0 end.

Fixpoint cal_inner' (m:nat) (n:nat) (s1:nat -> basisket) (s2:parstate) :=
   match m with 0 => C0
              | S j =>  Cplus (cal_inner_aux n (s1 j) s2) (cal_inner' j n s1 s2)
   end.
Definition cal_inner (n:nat) (s1:parstate) (s2:parstate) :=
   match s1 with Sup m p => cal_inner' m n p s2 | Zero => C0 end.

Fixpoint gen_plus (m:nat) (s:nat -> basisket) (t: partype) := 
  match m with 0 => (St Zero t)
             | S j => Plus (St (Sup 1 (fun a => if a =? 0 then s j else (C0, allzero))) t) (gen_plus j s t)
  end.

Inductive equiv : exp -> exp -> Prop :=
  | state_sum : forall m s t, 1 < m -> equiv (St (Sup m s) t) (gen_plus m s t)
  | alpha_1 : forall x y t ea, List.In y (freeVars ea) -> varCap ea y -> equiv (Lambda x t ea) (Lambda y t (subst ea x (Var y)))
  | alpha_2 : forall x y t ea, List.In y (freeVars ea) -> varCap ea y -> equiv (Mu x t ea) (Mu y t (subst ea x (Var y)))
  | plus_exb_1: forall ea eb ec, equiv (App (Plus ea eb) ec) (Plus (App ea ec) (App ea ec))
  | plus_exb_2: forall ea eb ec, equiv (App ec (Plus ea eb)) (Plus (App ec ea) (App ec ea))
  | plus_tensor_1: forall ea eb ec, equiv (Tensor (Plus ea eb) ec) (Plus (Tensor ea ec) (Tensor ea ec))
  | plus_tensor_2: forall ea eb ec, equiv (Tensor ec (Plus ea eb)) (Plus (Tensor ec ea) (Tensor ec ea))
  | trans_tensor: forall ea eb, equiv (Trans (Tensor ea eb)) (Tensor (Trans ea) (Trans eb))
  | trans_plus: forall ea eb, equiv (Trans (Plus ea eb)) (Plus (Trans ea) (Trans eb))
  | trans_app: forall ea eb, equiv (Trans (App ea eb)) (App (Trans eb) (Trans ea))
  | trans_mul: forall ea y t c, equiv (App ea (Trans (Lambda y t (Mul c (Var y))))) (Mul (Cconj c) ea)
  | trans_nor: forall ea, equiv (Trans (Nor ea)) (Nor (Trans ea))
  | tensor_app : forall e1 e2 e3 e4, equiv (App (Tensor e1 e2) (Tensor e3 e4)) (Tensor (App e1 e3) (App e2 e4)).


