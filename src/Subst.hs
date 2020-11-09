{-|
Module      : Subst
Description : Define las operaciones de la representacion locally nameless
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo define las operaciones de la representacion locally nameless,
y la substitución.

-}


module Subst where

import Lang
import Common
import Data.List ( elemIndex )

varChanger :: (Int -> Pos -> Name -> Term) --que hacemos con las variables localmente libres
           -> (Int -> Pos -> Int ->  Term) --que hacemos con los indices de De Bruijn
           -> Term -> Term
varChanger local bound t = go 0 t where
  go n   (V p (Bound i)) = bound n p i
  go n   (V p (Free x)) = local n p x 
  go n (Lam p y ty t)   = Lam p y ty (go (n+1) t)
  go n (App p l r)   = App p (go n l) (go n r)
  go n (Fix p f fty x xty t) = Fix p f fty x xty (go (n+2) t)
  go n (IfZ p c t e) = IfZ p (go n c) (go n t) (go n e)
  go n t@(Const _ _) = t
  go n (UnaryOp p op t) = UnaryOp p op (go n t)
  go n (Let p f ty t1 t2) = Let p f ty (go n t1) (go n t2)

-- `openN [nn,..,n0] t` reemplaza las primeras (n+1) variables ligadas
-- en `t` (que debe ser localmente cerrado) por los nombres libres en la
-- lista. La variable Bound 0 pasa a ser Free n0, y etc. Estos nombres
-- deben ser frescos en el término para que no ocurra shadowing.
openN :: [Name] -> Term -> Term
openN ns = varChanger (\_ p n -> V p (Free n)) bnd where
   bnd depth p i | i <  depth = V p (Bound i)
                 | i >= depth && i < depth + nns =
                    V p (Free (nsr !! (i - depth)))
                 | otherwise  = abort "openN: M is not LC"
   nns = length ns
   nsr = reverse ns

-- `closeN [nn,..,n0] t` es la operación inversa a open. Reemplaza
-- las variables `Free ni` por la variable ligada `Bound i`.
closeN :: [Name] -> Term -> Term
closeN ns = varChanger lcl (\_ p i -> V p (Bound i))
   where lcl depth p y =
            case elemIndex y nsr of
              Just i -> V p (Bound (i + depth))
              Nothing -> V p (Free y)
         nsr = reverse ns

-- `substN [tn,..,t0] t` sustituye los índices de de Bruijn en t con
-- los términos de la lista. Bound 0 pasa a t0, etc. Notar el orden
-- inverso para hacer las llamadas más intuitivas.
--
-- El término `t` debe tener a lo sumo tantos índices abiertos como la
-- longitud de la lista. Si es localmente cerrado (es decir que no tiene
-- índices abiertos), nada va a ser sustituido.
--
-- Puede pensarse como una optimizacíon de primero hacer `open
-- [nn,..,n0] t`, con nombres frescos, y luego sustituir los nombres
-- por los términos correspondientes. La ventaja es que no hace falta
-- generar ningún nombre, y por lo tanto evitamos la necesidad de
-- nombres frescos.
substN :: [Term] -> Term -> Term
substN ns = varChanger (\_ p n -> V p (Free n)) bnd
   where bnd depth p i 
             | i <  depth = V p (Bound i)
             | i >= depth && i < depth + nns
                = nsr !! (i - depth)
             | otherwise = abort "substN: M is not LC"
         nns = length ns
         nsr = reverse ns

-- Algunas definiciones auxiliares:

subst :: Term -> Term -> Term
subst n m = substN [n] m

close :: Name -> Term -> Term
close nm = closeN [nm]

open :: Name -> Term -> Term
open x t = openN [x] t
