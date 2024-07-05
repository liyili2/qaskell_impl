Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Permutations.
Require Import QuantumLib.VectorStates.
Require Import Lists.ListSet.
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

(*
Definition anti_s (s:state) (t:type) :=
   match s with Zero => Zero
             | Pair n1 n2 => Pair (t-n1) (t-n2)
   end.
*)

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

Fixpoint check_base (n:nat) (s:spinbase) (m:nat) :=
   match n with 0 => True
              | S j => check_base j s m /\ (s j) < m
   end.

Fixpoint good_base' (m:nat) (size:nat) (v:nat -> basisket) (n:nat) :=
  match m with 0 => True
            | S j => good_base' j size v n /\ check_base size (snd (v j)) n
  end.

Definition good_base (s:parstate) (n:partype) := 
  match s with Zero => True
             | Sup m v => good_base' m (fst n) v (snd n)
  end.

Inductive merge : type -> type -> type -> Prop :=
  | merge_st: forall s1 s2, merge (TType s1) (TType s2) (TType (TenType s1 s2))
  | merge_dot: forall s1 s2, merge (IType s1) (IType s2) (IType (TenType s1 s2))
  | merge_fun: forall f s1 s2, merge (FType f s1) (FType f s2) (FType f (TenType s1 s2)).

Inductive join : typeflag -> typeflag -> typeflag -> Prop :=
  | join_same : forall tf, join tf tf tf
  | join_p1 : forall tf, join P tf P
  | join_p2 : forall tf, join tf P P.

Inductive typing : (var -> type) -> exp -> type -> Prop :=
  | tpar : forall g t e1 e2, equiv e1 e2 -> typing g e2 t -> typing g e1 t
  | tvar : forall g x, typing g (Var x) (g x)
  | tvec : forall g s t, good_base s t -> typing g (St s t) t
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




