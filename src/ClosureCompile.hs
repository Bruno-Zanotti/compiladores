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
import Data.List ( isPrefixOf, nub )

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
                                          fx <- fresh x
                                          let vars = filter (isPrefixOf "__") (nub $ freeVars t)
                                          irt <- closureConvert $ open fx t
                                          clo <- fresh "clo"
                                          let irt' = foldr (\(v, i) t -> IrLet v (IrAccess (IrVar clo) i) t) irt (zip vars [1..])
                                          writer (MkClosure n (map IrVar vars), [IrFun n [clo, fx] irt'])
closureConvert (App _ (V _ (Free n)) x) = do irx <- closureConvert x
                                             return (IrCall (IrAccess (IrVar n) 0) [IrVar n, irx])
closureConvert (App _ f x)           = do irf <- closureConvert f
                                          irx <- closureConvert x
                                          clo <- fresh "clo"
                                          return (IrLet clo irf (IrCall (IrAccess (IrVar clo) 0) [IrVar clo, irx]))
closureConvert (BinaryOp _ op t1 t2) = do irt1 <- closureConvert t1
                                          irt2 <- closureConvert t2
                                          return (IrBinaryOp op irt1 irt2)
closureConvert (Fix _ f _ x _ t)     = do n <- fresh ""
                                          ff <- fresh f
                                          fx <- fresh x
                                          let args = [ff, fx]
                                          let vars = filter (isPrefixOf "__") (nub $ freeVars t)
                                          irt <- closureConvert $ openN args t
                                          clo <- fresh "clo"
                                          let irt' = foldr (\(v, i) t -> IrLet v (IrAccess (IrVar clo) i) t) irt (zip vars [1..])
                                          writer (MkClosure n (map IrVar vars), [IrFun n [clo, fx] (IrLet ff (IrVar clo) irt')])
closureConvert (IfZ _ c t f)         = do irc <- closureConvert c
                                          irt <- closureConvert t
                                          irf <- closureConvert f
                                          return (IrIfZ irc irt irf)
closureConvert (Let _ v _ t1 t2)     = do irt1 <- closureConvert t1
                                          fv <- fresh v
                                          irt2 <- closureConvert (open fv t2)
                                          return (IrLet fv irt1 irt2)

fresh :: Monad m => String -> StateT Int m Name
fresh n = do s <- get
             put (s+1)
             return ("__" ++ n ++ show s)

runCC :: [Decl Term] -> [IrDecl]
runCC xs = runCC' xs 0

runCC' :: [Decl Term] -> Int -> [IrDecl]
runCC' [] _ = []
runCC' (Decl _ name b :xs) n = decls ++ IrVal name irtm : runCC' xs n'
                            where ((irtm, n'), decls) = runWriter (runStateT (closureConvert b) n)