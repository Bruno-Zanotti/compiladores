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

module Elab ( elab, elab_decl, desugarDecl, elab' ) where

import Lang
    ( SNTerm,
      STm(SLam, SV, SConst, SApp, SUnaryOp, SIfZ, SLet, SRec, SFix),
      Var(Free),
      Term,
      NTerm,
      Tm(Lam, V, Const, UnaryOp, Fix, IfZ, App),
      Decl(Decl),
      Ty(FunTy),
      SDecl(SDRec, SDLet) )
import Subst

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

elab :: SNTerm -> Term
elab = elab' . desugar

elab_decl :: SDecl SNTerm -> Decl Term
elab_decl = fmap elab' . desugarDecl

-- | 'desugar' remueve el azucar sintáctico de los términos
desugar :: SNTerm -> NTerm
desugar (SV p v)                 = V p v
desugar (SConst p c)             = Const p c
desugar (SLam p vs st)           = case vs of
                                    [(x, ty)]  -> Lam p x ty (desugar st)
                                    (x, ty):xs -> Lam p x ty (desugar (SLam p xs st))
desugar (SApp p st1 st2)         = App p (desugar st1) (desugar st2)
desugar (SUnaryOp p o st)        = UnaryOp p o (desugar st)
desugar (SFix p f fty x xty st)  = Fix p f fty x xty (desugar(st))
desugar (SIfZ p st1 st2 st3)     = IfZ p (desugar st1) (desugar st2) (desugar st3)
desugar (SLet p f vs ty st1 st2) = case vs of
                                    []          -> App p (Lam p f ty (desugar st2)) (desugar st1)
                                    (x, xty):xs -> desugar (SLet p f xs (FunTy xty ty) (SLam p [(x, xty)] st1) st2) 
desugar (SRec p f vs ty st1 st2) = case vs of
                                    [(x, xty)] -> desugar (SLet p f [] (FunTy xty ty) (SFix p f (FunTy xty ty) x xty st1) st2) 
                                    x:xs       -> desugar (SRec p f [x] (FunTy (getType xs) ty) (SLam p xs st1) st2)

desugarDecl :: SDecl SNTerm -> Decl NTerm
desugarDecl (SDLet p v [] _ st)            = Decl p v (desugar st)
desugarDecl (SDLet p v vs _ st)            = Decl p v (desugar (SLam p vs st))
desugarDecl (SDRec p v [(x, xty)] ty st)   = desugarDecl (SDLet p v [] ty (SFix p v (FunTy xty ty) x xty st))
desugarDecl (SDRec p v ((x,xty):xs) ty st) = desugarDecl (SDRec p v [(x, xty)] (FunTy (getType xs) ty) (SLam p xs st))

getType :: [(a, Ty)] -> Ty
getType [(_, xty)]    = xty
getType ((_, xty):xs) = FunTy xty (getType xs)