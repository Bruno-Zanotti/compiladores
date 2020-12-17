{-|
Module      : Closure Compile
Description : Compila Funciones de Alto Orden
Copyright   : (c) Eric Vernaschi, Bruno Zanotti, 2020.
License     : GPL-3
Maintainer  : -
Stability   : experimental
Este módulo permite compilar compila funciones de alto orden a través de la
conversión de clausuras.
-}

module ClosureCompile where
import Lang 
import Subst
import MonadPCF
import Control.Monad.State
import Control.Monad.Writer

data IrTm = IrVar Name
         | IrCall IrTm [IrTm]
         | IrConst Const
         | IrBinaryOp BinaryOp IrTm IrTm
         | IrLet Name IrTm IrTm
         | IrIfZ IrTm IrTm IrTm
         | MkClosure Name [IrTm]
         | IrAccess IrTm Int
         deriving (Show)

data IrDecl = IrVal {irDeclName :: Name, irDeclDef :: IrTm}
            | IrFun {irDeclName :: Name, irDeclArgNames :: [Name], irDeclBody :: IrTm}
            deriving (Show)

closureConvert :: Term -> StateT Int (Writer [IrDecl]) IrTm
closureConvert (V _ (Free n))        = return (IrVar n)
closureConvert (Const _ n)           = return (IrConst n)
closureConvert (Lam _ x _ t)         = do n <- fresh ""
                                          arg <- fresh x
                                          let vars = freeVars t
                                          irt <- closureConvert (open arg t)
                                          clo <- fresh "clo"
                                          writer (MkClosure n (map IrVar vars), [IrFun n [clo, arg] irt])
closureConvert (App _ f x)           = do clos <- closureConvert f
                                          irx <- closureConvert x
                                          return (IrCall (IrAccess clos 0) [clos, irx])
closureConvert (BinaryOp _ op t1 t2) = do irt1 <- closureConvert t1
                                          irt2 <- closureConvert t2
                                          return (IrBinaryOp op irt1 irt2)
closureConvert (Fix _ f _ x _ t)     = do n <- fresh ""
                                          ff <- fresh f
                                          fx <- fresh x
                                          let args = [ff, fx]
                                          let vars = freeVars t
                                          irt <- closureConvert (openN args t)
                                          clo <- fresh "clo"
                                          let irl = IrLet ff (IrVar clo) irt
                                          writer (MkClosure n (map IrVar vars), [IrFun n [clo,fx] irl])
closureConvert (IfZ _ c t f)         =  do irc <- closureConvert c
                                           irt <- closureConvert t
                                           irf <- closureConvert f
                                           return (IrIfZ irc irt irf)
closureConvert (Let _ n _ t1 t2)     = do irt1 <- closureConvert t1
                                          irt2 <- closureConvert t2
                                          return (IrLet n irt1 irt2)

fresh :: Monad m => String -> StateT Int m Name
fresh n = do s <- get
             put (s+1)
             return ("__" ++ n ++ show s)

runCC :: [Decl Term] -> [IrDecl]
runCC xs = runCC' xs 0

runCC' :: [Decl Term] -> Int -> [IrDecl]
runCC' [] _ = []
runCC' (Decl _ name b :xs) n = snd res ++ IrVal name (fst (fst res)) : runCC' xs (snd (fst res))
                            where res = runWriter (runStateT (closureConvert b) n)