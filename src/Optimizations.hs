{-|
Module      : Optimizations
Description : Compila Funciones de Alto Orden
Copyright   : (c) Eric Vernaschi, Bruno Zanotti, 2020.
License     : GPL-3
Maintainer  : -
Stability   : experimental
Este aplica las distintas optimizaciones sobre el código.
-}

module Optimizations where

import Lang
import Subst
import MonadPCF
import Common ( Pos(NoPos) )

optimization :: MonadPCF m => [Decl Term] -> m [Decl Term]
optimization [] = return []
optimization xs = inLineExpansion xs 0

inLineExpansion :: MonadPCF m => [Decl Term] -> Int -> m [Decl Term]
inLineExpansion [] _ = return []
inLineExpansion xs 0 = return xs
inLineExpansion xs n = do xs' <- mapM expandDecl xs
                          inLineExpansion xs' (n-1)

expandDecl :: MonadPCF m => Decl Term -> m (Decl Term)
expandDecl (Decl i n t) = Decl i n <$> expand t

expand :: MonadPCF m => Term -> m Term
expand fv@(V p (Free v)) = do def <- lookupDecl v
                              case def of
                                Nothing          -> return fv
                                Just IfZ {}      -> return fv
                                Just BinaryOp {} -> return fv
                                Just App {}      -> return fv
                                Just t           -> return t
expand (Lam p x ty t)         = Lam p x ty <$> expand t
expand (App _ (Lam _ _ _ t) arg) = case arg of
                                     (V _ (Free _)) -> return (subst arg t)
                                    --  (V p (Bound n)) -> return (subst (V p (Bound (n+1))) t)
                                     (Const _ _) -> return (subst arg t)
                                     _           -> do let z = "z123"
                                                      --  z' <- fresh "z"
                                                      --  arg' <- expand arg
                                                      --  let t' = subst (V NoPos (Free z)) t
                                                       return (Let NoPos z NatTy arg t)
expand (App p t u)            = App p <$> expand t <*> expand u
expand (Fix p f' fty x xty t) = Fix p f' fty x xty <$> expand t 
expand (IfZ p c t e)          = IfZ p <$> expand c <*> expand t <*> expand e
expand (Let p f ty t1 t2)     = Let p f ty <$> expand t1 <*> expand t2
expand (BinaryOp i o t1 t2)   = BinaryOp i o <$> expand t1<*> expand t2
expand t                      = return t

fresh :: Name -> State Int Name
fresh name = do s <- get
                put (s+1)
                return (name ++"_"++ show s)