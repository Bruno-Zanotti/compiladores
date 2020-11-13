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
      STm(SLam, SV, SConst, SApp, SUnaryOp, SIfZ, SLet, SRec, SFix),
      Var(Free),
      Term,
      NTerm,
      Tm(Lam, V, Const, UnaryOp, Fix, IfZ, App, Let),
      Decl(Decl),
      Ty(NatTy, FunTy),
      STy(SNatTy, SFunTy, SNamedTy),
      SDecl(SDRec, SDLet, SDType) )
import Subst
import MonadPCF (lookupTy, MonadPCF, failPosPCF)
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
elab' (UnaryOp i o t)       = UnaryOp i o (elab' t)
elab' (Let p f ty t1 t2)    = Let p f ty (elab' t1) (close f (elab' t2))

elab :: MonadPCF m => SNTerm -> m Term
elab st = do
  t <- desugar st
  return (elab' t)

-- | 'desugar' remueve el azucar sintáctico de los términos
desugar :: MonadPCF m => SNTerm -> m NTerm
desugar (SV p v)                            = return (V p v)
desugar (SConst p c)                        = return (Const p c)
desugar (SLam p [(x, ty)] st)               = Lam p x <$> desugarTy ty <*> desugar st
desugar (SLam p ((x, ty):xs) st)            = Lam p x <$> desugarTy ty <*> desugar (SLam p xs st)
desugar (SApp p st1 st2)                    = App p <$> desugar st1 <*> desugar st2
desugar (SUnaryOp p o Nothing)              = desugar(SLam p [("x", SNatTy)] (SUnaryOp p o (Just (SV p "x"))))
desugar (SUnaryOp p o (Just st))            = UnaryOp p o <$> desugar st
desugar (SFix p f fty x xty st)             = Fix p f <$> desugarTy fty <*> return x <*> desugarTy xty <*> desugar st
desugar (SIfZ p st1 st2 st3)                = IfZ p <$> desugar st1 <*> desugar st2 <*> desugar st3
-- desugar (SLet p f [] ty st1 st2)            = App p <$> (Lam p f <$> desugarTy ty <*> desugar st2) <*> desugar st1
-- desugar (SLet p f ((x, xty):xs) ty st1 st2) = desugar (SLet p f xs (SFunTy xty ty) (SLam p [(x, xty)] st1) st2) 
desugar (SLet p f [] ty st1 st2)            = Let p f <$> desugarTy ty <*> desugar st1 <*> desugar st2
desugar (SLet p f ((x, xty):xs) ty st1 st2) = desugar (SLet p f xs (SFunTy xty ty) (SLam p [(x, xty)] st1) st2) 
desugar (SRec p f [(x, xty)] ty st1 st2)    = desugar (SLet p f [] (SFunTy xty ty) (SFix p f (SFunTy xty ty) x xty st1) st2) 
desugar (SRec p f (x:xs) ty st1 st2)        = desugar (SRec p f [x] (SFunTy (getType xs) ty) (SLam p xs st1) st2)

desugarDecl :: MonadPCF m => SDecl SNTerm -> m (Decl NTerm)
desugarDecl (SDLet p v [] _ st)            = Decl p v <$> desugar st
desugarDecl (SDLet p v vs _ st)            = Decl p v <$> desugar (SLam p vs st)
desugarDecl (SDRec p v [(x, xty)] ty st)   = desugarDecl (SDLet p v [] ty (SFix p v (SFunTy xty ty) x xty st))
desugarDecl (SDRec p v ((x,xty):xs) ty st) = desugarDecl (SDRec p v [(x, xty)] (SFunTy (getType xs) ty) (SLam p xs st))
-- TODO: ver
desugarDecl (SDType p _ _) = failPosPCF p "Declaración de tipo inválida"

desugarTy :: MonadPCF m => STy -> m Ty
desugarTy SNatTy         = return NatTy
desugarTy (SFunTy t1 t2) =  FunTy <$> desugarTy t1 <*>  desugarTy t2
desugarTy (SNamedTy n)   = do 
                          mty <- lookupTy n
                          case mty of
                            Just ty -> return ty
                            _       -> failPosPCF NoPos $ "No existe el tipo: " ++ n

getType :: [(a, STy)] -> STy
getType [(_, xty)]    = xty
getType ((_, xty):xs) = SFunTy xty (getType xs)