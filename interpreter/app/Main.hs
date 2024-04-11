module Main (main) where

import Lib

main :: IO ()
main = someFunc

data State = Pair Int Int | Zero deriving (Show)

data Sigma = Up | Down deriving (Show)

type Type = Int

data Exp = St State Type
	| Anni Sigma
	| Trans Exp
	| Tensor Exp Exp
	| App Exp Exp deriving (Show)
	
anti_s :: State -> Type -> State
anti_s Zero _ = Zero
anti_s (Pair n1 n2) t = Pair (t - n1) (t - n2)

sem :: Exp -> Exp -> Bool
sem (App (Anni s) (St Zero n)) (St Zero n) = True 								-- anni_0
sem (App (Anni Up) (St (Pair 0 n) t)) (St Zero t) = True 						-- anni_bot_l
sem (App (Anni Down) (St (Pair n 0) t)) (St Zero t) = True						-- anni_bot_r
sem (App (Anni Up) (St (Pair n1 n2) t)) (St (Pair (n1 - 1) n2) t)				-- anni_l
	| n1 > 0 = True
sem (App (Anni Down) (St (Pair n1 n2) t)) (St (Pair n1 (n2 - 1) t)				-- anni_r
	| n2 > 0 = True
sem (App e (St (anti_s s t) t)) (St s' t)										-- trans_app
	| sem (App (Trans e) (St s t)) (St (anti_s s' t) t) = True
sem (App (Tensor e1 e2) (Tensor e3 e4)) (Tensor (App e1 e3) (App e2 e4)) = True	-- tensor_app
