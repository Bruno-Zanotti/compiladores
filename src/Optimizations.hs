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
optimization (df@(Decl _ f (Lam _ v _ t1)) :xs) = do op <- optimization (inLineExpansion xs f t1)
                                                     return (df:op)
optimization (decl:xs) =  do op <- optimization xs
                             return (decl:op)
optimization [] = return []
-- optimization decl = failPCF $ "Declaración inválida:\n" ++ show decl
--  Decl f: Fun (x:NatTy) -> Fun (y:NatTy) -> Res (Bound 1) (Bound 0) ----->>>> f 3 ---->>> APP (Fun (y:NatTy) -> Res (Bound 1) (Bound 0)) 3

inLineExpansion :: [Decl Term] -> Name -> Term -> [Decl Term]
inLineExpansion (Decl p name term :xs) f def = Decl p name (evalState (expand term f def) 0) : inLineExpansion xs f def
-- inLineExpansion (decl : xs) f def = decl : inLineExpansion xs f def
inLineExpansion [] _ _ = []

-- let f1 (x y:Nat):Nat = res x 1 => res (Bound 1) 1
-- let r (z :Nat): Nat = f1 (Bound 0) 1 => fun (z: Nat) = res (Bound 0) 1 =>  
-- let a: Nat = r 1

expand :: Term -> Name -> Term -> State Int Term
expand (Lam p x ty t) f def         = Lam p x ty <$> expand t f def 
expand (App p v@(V p' (Free f')) arg) f def = if f' == f
                                              then case arg of
                                                     V p (Free v') -> return (subst (V p (Free v')) def)
                                                     V p (Bound n) -> return (subst (V p (Bound n)) def)
                                                     Const p c     -> return (subst (Const p c) def)
                                                     _             -> do var <- fresh "z"
                                                                         v' <- expand arg f def 
                                                                         let a = subst (V NoPos (Free var)) def
                                                                         return (Let NoPos var NatTy v' a)
                                                                        --  return (subst (go v') def)
                                              else App p' v <$> expand arg f def
expand (App p t u) f def            = App p <$> expand t f def <*> expand u f def
expand (Fix p f' fty x xty t) f def = Fix p f' fty x xty <$> expand t f def 
expand (IfZ p c t e) f def          = IfZ p <$> expand c f def <*> expand t f def <*> expand e f def
expand (BinaryOp i o t1 t2) f def   = BinaryOp i o <$> expand t1 f def <*> expand t2 f def
expand t _ _                        = return t

fresh :: Name -> State Int Name
fresh name = do s <- get
                put (s+1)
                return (name ++"_"++ show s)
