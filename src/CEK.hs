{-|
Module      : CEK
Description : Define una Máquina Abstracta para guiar la implementación.
Copyright   : (c) Eric Vernaschi, Bruno Zanotti, 2020.
License     : GPL-3
Maintainer  : -
Stability   : experimental

-}

module CEK where

import Lang
import Common
import MonadPCF
import PPrint
import Subst ( substN )

-- | Valores
data Val = 
      N Int
    | Clos Clos
    deriving (Show)

-- | Clausura
data Clos =
      CFun Env Name Ty Term
    | CFix Env Name Ty Name Ty Term 
    | CLet Env Name Ty Term Term 
    deriving (Show)

-- | Entorno
type Env = [Val]

-- | Frames
-- | fr ::= ρ ·[] t
--       | clos []
--       | ρ · ifz [] then t else e
--       | succ []
--       | pred []
data Frames = 
      KArg Env Term
    | KClos Clos
    | KIf Env Term Term
    | KSucc 
    | KPred
    | KLet Env Term
    deriving (Show)

-- | Continuaciones
type Kont = [Frames]

search :: MonadPCF m => Term -> Env -> Kont -> m Val
search (UnaryOp _ Pred t) e k = search t e (KPred:k)
search (UnaryOp _ Succ t) e k = search t e (KSucc:k)
search (IfZ _ t1 t2 t3) e k   = search t1 e (KIf e t2 t3:k)
search (App _ t1 t2) e k      = search t1 e (KArg e t2:k)
search (V _ (Bound v)) e k    = destroy (e!!v) k
search (V _ (Free v)) e k     = do 
  mv <- lookupDecl v 
  case mv of 
    Nothing -> failPCF $ "Error de ejecución: variable no declarada: " ++ ppName v
    Just t  -> search t e k
search (Const _ (CNat c)) _ k     = destroy (N c) k
search (Lam _ x xty t) e k        = destroy (Clos (CFun e x xty t)) k
search (Fix _ f fty x xty t) e k  = destroy (Clos (CFix e f fty x xty t)) k
search (Let _ _ _ t1 t2) e k    = search t1 e (KLet e t2:k)

destroy :: MonadPCF m => Val -> Kont -> m Val
destroy v []                                 = return v
destroy (N 0) (KPred:k)                      = destroy (N 0) k
destroy (N n) (KPred:k)                      = destroy (N (n-1)) k
destroy (N n) (KSucc:k)                      = destroy (N (n+1)) k
destroy (N 0) ((KIf e t _):k)                = search t e k
destroy (N _) ((KIf e _ f):k)                = search f e k
destroy (Clos c) ((KArg e t):k)              = search t e (KClos c:k)
destroy v ((KClos (CFun e _ _ t):k))         = search t (v:e) k
destroy v ((KClos (CFix e f fty x xty t)):k) = search t (v:Clos (CFix e f fty x xty t):e) k
destroy v ((KLet e t):k)                     = search t (v:e) k
destroy _ _ = failPCF "Fallo de evaluacion en el destroy"


valToTerm :: Val -> Term
valToTerm (N n) = Const NoPos (CNat n)
valToTerm (Clos (CFun e x xty t))       = substN (map valToTerm e) (Lam NoPos x xty t)
valToTerm (Clos (CFix e f fty x xty t)) = substN (map valToTerm e) (Fix NoPos f fty x xty t)

eval :: MonadPCF m => Term -> m Term
eval t = do v <- search t [] []
            return (valToTerm v)
