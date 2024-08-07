module Main (main) where

import Lib


main :: IO ()
main = someFunc

type State = [Int]

type Sigma = Int

type Type = (Int , Int)

data Op = Anni | Crea
	deriving (Show)

data Exp = I
        | Hold State
	| Single Op Sigma Type
	| Plus Exp Exp
	| Tensor Exp Exp
	| App Exp Exp
	deriving (Show)
	
data Con = Var String
        | Val [[Int]]
	| Let String Exp Con
	| Sum Con Con
	| Times Int Con
	deriving (Show)
	
--anti_s :: State -> Type -> State
--anti_s Zero _ = Zero
--anti_s (Pair n1 n2) t = Pair (t - n1) (t - n2)

gen_tensor :: Int -> Exp
gen_tensor 0 = I
gen_tensor n =  Tensor (gen_tensor (n - 1)) I

gen_list 0 = []
gen_list n = 0:(gen_list (n-1))

setAt i v l = (take i l) ++ (v:(drop (i+1) l))

gen_num :: Op -> Int -> State -> Exp
gen_num Anni s l = Hold l
gen_num Crea s l = Hold (setAt s 1 l)

equiv :: Exp -> Exp
equiv (App I I) = I
equiv (App (Plus e1 e2) e) = Plus (App e1 e) (App e2 e)
equiv (App (Tensor e1 e2) (Tensor e3 e4)) = Tensor (App e1 e3) (App e2 e4)
equiv (App (Single op s t) I) = Tensor (gen_tensor s) (Tensor (gen_num op s (gen_list (fst t))) (gen_tensor (fst t - s - 1))) 

interInt [1,0] = -1
interInt [0,1] = 1
interInt [0] = 0
interInt [1] = 1

interAux (Hold l) = [interInt l]
interAux (Tensor e1 e2) = interAux e1 ++ interAux e2

inter :: Exp -> [[Int]]
inter (Hold l) = [l]
inter (Tensor e1 e2) = [interAux (Tensor e1 e2)]
inter (Plus e1 e2) = inter e1 ++ inter e2

subst (Var x) y e = if x == y then Val e else (Var x)
subst (Val v) y e = Val v
subst (Let x e v) y ea = if x == y then Let x e v else Let x e (subst v y ea)
subst (Sum e1 e2) y ea = Sum (subst e1 y ea) (subst e2 y ea)
subst (Times e1 e2) y ea = Times e1 (subst e2 y ea)

listAddAux [] [] = []
listAddAux (v1:vl) (x1:xl) = (v1+x1):(listAddAux vl xl)

listAddA :: [Int] -> [[Int]] -> [[Int]]
listAddA v [] = []
listAddA v (x1:xl) = (listAddAux v x1) : listAddA v xl

listAdd :: [[Int]] -> [[Int]] -> [[Int]]
listAdd [] vl = []
listAdd (v1:vl) xl = listAddA v1 xl ++ listAdd vl xl


listTimesAux v [] = []
listTimesAux v (x:xl) = v * x : listTimesAux v xl

listTimes :: Int -> [[Int]] -> [[Int]]
listTimes v [] = []
listTimes v (x:xl) = (listTimesAux v x):(listTimes v xl)


dealC (Let x v c) = dealC (subst c x (inter (equiv v)))
dealC (Val xl) = xl
dealC (Sum e1 e2) = let v1 = dealC e1 in let v2 = dealC e2 in listAdd v1 v2
dealC (Times a e) = let v = dealC e in listTimes a v





