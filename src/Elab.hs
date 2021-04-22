{-|
Module      : Elab
Description : Elabora un término fully named a uno locally closed.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite elaborar términos y declaraciones para convertirlas desde
fully named (@NTerm) a locally closed (@Term@) 
-}

module Elab ( elab, desugarDecl, elab', desugarTy ) where

import Lang
    ( SNTerm,
      STm(SLam, SV, SConst, SApp, SUnaryOp, SBinaryOp, SIfZ, SLet, SRec, SFix),
      Var(Free),
      Term,
      UnaryOp(..),
      Const(..),
      BinaryOp(..),
      NTerm,
      Tm(Lam, V, Const, BinaryOp, Fix, IfZ, App, Let),
      Decl(Decl),
      Ty(NatTy, FunTy),
      STy(SNatTy, SFunTy, SNamedTy),
      SDecl(SDRec, SDLet, SDType) )
import Subst
import MonadPCF (lookupTy, MonadPCF, failPosPCF, addTy, failPCF)
import Common ( Pos(NoPos) )

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab' :: NTerm -> Term
elab' (V p v)               = V p (Free v)
elab' (Const p c)           = Const p c
elab' (Lam p v ty t)        = Lam p v ty (close v (elab' t))
elab' (App p h a)           = App p (elab' h) (elab' a)
elab' (Fix p f fty x xty t) = Fix p f fty x xty (closeN [f, x] (elab' t))
elab' (IfZ p c t e)         = IfZ p (elab' c) (elab' t) (elab' e)
elab' (BinaryOp i o t1 t2)  = BinaryOp i o (elab' t1) (elab' t2)
elab' (Let p f ty t1 t2)    = Let p f ty (elab' t1) (close f (elab' t2))

elab :: MonadPCF m => SNTerm -> m Term
elab st = do
  t <- desugar st
  return (elab' t)

-- | 'desugar' remueve el azucar sintáctico de los términos
desugar :: MonadPCF m => SNTerm -> m NTerm
desugar (SV p v)                              = return (V p v)
desugar (SConst p c)                          = return (Const p c)
desugar (SLam p [(x, ty)] st)                 = Lam p x <$> desugarTy ty <*> desugar st
desugar (SLam p ((x, ty):xs) st)              = Lam p x <$> desugarTy ty <*> desugar (SLam p xs st)
desugar (SApp p st1 st2)                      = App p <$> desugar st1 <*> desugar st2
desugar (SUnaryOp p o Nothing)                = desugar(SLam p [("x", SNatTy)] (SUnaryOp p o (Just (SV p "x"))))
desugar (SUnaryOp p Succ (Just st))           = BinaryOp p Sum <$> desugar st <*> desugar (SConst p (CNat 1))
desugar (SUnaryOp p Pred (Just st))           = BinaryOp p Res <$> desugar st <*> desugar (SConst p (CNat 1))
desugar (SBinaryOp p o Nothing Nothing)       = desugar(SLam p [("x", SNatTy), ("y", SNatTy)] (SBinaryOp p o (Just (SV p "x"))(Just (SV p "y"))))
desugar (SBinaryOp p o (Just st) Nothing)     = desugar(SLam p [("x", SNatTy)] (SBinaryOp p o (Just st) (Just (SV p "x"))))
desugar (SBinaryOp p o (Just st1) (Just st2)) = BinaryOp p o <$> desugar st1 <*> desugar st2
desugar (SFix p f fty x xty st)               = Fix p f <$> desugarTy fty <*> return x <*> desugarTy xty <*> desugar st
desugar (SIfZ p st1 st2 st3)                  = IfZ p <$> desugar st1 <*> desugar st2 <*> desugar st3
desugar (SLet p f [] ty st1 st2)              = Let p f <$> desugarTy ty <*> desugar st1 <*> desugar st2
desugar (SLet p f ((x, xty):xs) ty st1 st2)   = desugar (SLet p f xs (SFunTy xty ty) (SLam p [(x, xty)] st1) st2) 
desugar (SRec p f [(x, xty)] ty st1 st2)      = desugar (SLet p f [] (SFunTy xty ty) (SFix p f (SFunTy xty ty) x xty st1) st2) 
desugar (SRec p f (x:xs) ty st1 st2)          = desugar (SRec p f [x] (SFunTy (getType xs) ty) (SLam p xs st1) st2)

desugarDecl :: MonadPCF m => SDecl SNTerm -> m (Maybe (Decl NTerm))
desugarDecl (SDLet p v [] _ st)            = Just . Decl p v <$> desugar st
desugarDecl (SDLet p v vs _ st)            = Just . Decl p v <$> desugar (SLam p vs st)
desugarDecl (SDRec p v [(x, xty)] ty st)   = desugarDecl (SDLet p v [] ty (SFix p v (SFunTy xty ty) x xty st))
desugarDecl (SDRec p v ((x,xty):xs) ty st) = desugarDecl (SDRec p v [(x, xty)] (SFunTy (getType xs) ty) (SLam p xs st))
desugarDecl (SDType p v sty) = do ty <- desugarTy sty
                                  addTy v ty
                                  return Nothing
desugarDecl _ = failPCF "Declaración inválida"

desugarTy :: MonadPCF m => STy -> m Ty
desugarTy SNatTy         = return NatTy
desugarTy (SFunTy t1 t2) =  FunTy <$> desugarTy t1 <*>  desugarTy t2
desugarTy (SNamedTy n)   = do 
                          mty <- lookupTy n
                          case mty of
                            Just ty -> return ty
                            _       -> failPCF $ "No existe el tipo: " ++ n

getType :: [(a, STy)] -> STy
getType [(_, xty)]    = xty
getType ((_, xty):xs) = SFunTy xty (getType xs)