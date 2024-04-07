

Inductive state := Pair (n1:nat) (n2:nat) | Zero.

Inductive sigma := Up | Down.

Definition type :Set := nat.

Inductive exp := 
        | St (s:state) (t:type)
        | Anni (s:sigma)
        | Trans (e:exp)
        | Tensor (e1:exp) (e2:exp)
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