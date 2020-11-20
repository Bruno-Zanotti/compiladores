{-|
Module      : PPrint
Description : Pretty printer para PCF.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module PPrint (
    pp,
    ppTy,
    ppName
    ) where

import Prelude hiding ((<>))
import Lang
import Subst
import Text.PrettyPrint

-- Como `openN`, pero cambia el nombre si genera shadowing. Nota:
-- esto es rídiculamente ineficiente si los términos empiezan a ser
-- grandes, porque requiere atravesarlo íntegramente.
openRename :: [Name] -> Term -> ([Name], Term)
openRename ns t =
  let fs = freeVars t in
  let freshen n = let cands = n : map (\i -> n ++ show i) [0..] in
                  let n' = head (filter (\n -> notElem n fs) cands) in
                  n'
  in
  let fresh_ns = map freshen ns in
  (fresh_ns, openN fresh_ns t)

-- | 'openAll' convierte términos locally nameless
-- a términos fully named abriendo todos las variables de ligadura que va encontrando
-- Debe tener cuidado de no abrir términos con nombres que ya fueron abiertos.
openAll :: Term -> NTerm
openAll (V p v) = case v of 
      Bound i ->  V p $ "(Bound "++show i++")" --este caso no debería aparecer
                                               --si el término es localmente cerrado
      Free x -> V p x 
openAll (Const p c) = Const p c
openAll (Lam p x ty t) =
    let ([x'], t') = openRename [x] t in
    Lam p x' ty (openAll t')
openAll (App p t u) = App p (openAll t) (openAll u)
openAll (Fix p f fty x xty t) =
    let ([f', x'], t') = openRename [f, x] t in
    Fix p f' fty x' xty (openAll t')
openAll (IfZ p c t e) = IfZ p (openAll c) (openAll t) (openAll e)
openAll (BinaryOp i o t1 t2) = BinaryOp i o (openAll t1) (openAll t2)

-- | Pretty printer de nombres (Doc)
name2doc :: Name -> Doc
name2doc = text

-- |  Pretty printer de nombres (String)
ppName :: Name -> String
ppName = id

-- | Pretty printer para tipos (Doc)
ty2doc :: Ty -> Doc
ty2doc NatTy     = text "Nat"
ty2doc (FunTy x@(FunTy _ _) y) = sep [parens (ty2doc x),text "->",ty2doc y]
ty2doc (FunTy x y) = sep [ty2doc x,text "->",ty2doc y] 

-- | Pretty printer para tipos (String)
ppTy :: Ty -> String
ppTy = render . ty2doc

c2doc :: Const -> Doc
c2doc (CNat n) = text (show n)

unary2doc :: UnaryOp -> Doc
unary2doc Succ = text "succ"
unary2doc Pred = text "pred"

binary2doc :: BinaryOp -> Doc
binary2doc Sum = text "sum"
binary2doc Res = text "res"

collectApp :: NTerm -> (NTerm, [NTerm])
collectApp t = go [] t where
  go ts (App _ h t) = go (t:ts) h
  go ts h = (h, ts)

parenIf :: Bool -> Doc -> Doc
parenIf True = parens
parenIf _ = id

-- t2doc at t :: Doc
-- at: debe ser un átomo
-- | Pretty printing de términos (Doc)
t2doc :: Bool     -- Debe ser un átomo? 
      -> NTerm    -- término a mostrar
      -> Doc
-- Uncomment to use the Show instance for STerm
{- t2doc at x = text (show x) -}
t2doc _ (V _ x) = text x
t2doc _ (Const _ c) = c2doc c
t2doc at (Lam _ v ty t) =
  parenIf at $
  sep [sep [text "fun", parens (sep [name2doc v,text ":",ty2doc ty]), text "->"], nest 2 (t2doc False t)]

t2doc at t@App {} =
  let (h, ts) = collectApp t in
  parenIf at $
  t2doc True h <+> sep (map (t2doc True) ts)

t2doc at (Fix _ f fty x xty m) =
  parenIf at $
  sep [ sep [ text "fix", binding2doc (f, fty), binding2doc (x, xty), text "->" ]
      , nest 2 (t2doc False m)
      ]

t2doc at (IfZ _ c t e) =
  parenIf at $
  sep [ text "ifz", nest 2 (t2doc False c)
      , text "then", nest 2 (t2doc False t)
      , text "else", nest 2 (t2doc False e) ]

t2doc at (BinaryOp _ o t1 t2) =
  parenIf at $
  binary2doc o <+> t2doc True t1 <+> t2doc True t2

binding2doc (x, ty) =
  parens (sep [name2doc x, text ":", ty2doc ty])

-- | Pretty printing de términos (String)
pp :: Term -> String
-- Uncomment to use the Show instance for Term
{- pp = show -}
pp = render . t2doc False . openAll


