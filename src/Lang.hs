{-# LANGUAGE DeriveFunctor #-}

{-|
Module      : Lang
Description : AST de términos, declaraciones y tipos
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Definiciones de distintos tipos de datos:
  - AST de términos
  - Declaraciones
  - Tipos
  - Variables

-}

module Lang where

import Common ( Pos )
import Data.List

-- | AST de Tipos
data Ty = 
      NatTy 
    | FunTy Ty Ty
    deriving (Show,Eq)

-- | AST de Tipos azucarados
data STy = 
      SNatTy 
    | SFunTy STy STy
    | SNamedTy Name
    deriving (Show,Eq)

type Name = String

newtype Const = CNat Int

instance Show Const where
  show (CNat a) = show a

data UnaryOp = Succ | Pred
  deriving Show

data BinaryOp = Sum | Res
  deriving Show

-- | tipo de datos de declaraciones, parametrizado por el tipo del cuerpo de la declaración
data Decl a =
    Decl { declPos :: Pos, declName :: Name, declBody :: a }
  | Eval a
  deriving (Functor)

instance (Show a) => Show (Decl a) where
  show (Decl p name body) = name ++ ": " ++ show body
  show (Eval a) = show a

-- | tipo de datos de declaraciones azucaradas
data SDecl a =
    SDLet  { sDeclPos :: Pos, sDeclName :: Name, sDeclBindings :: [(Name, STy)], sDeclType :: STy, sDeclBody :: a }
  | SDRec  { sDeclPos :: Pos, sDeclName :: Name, sDeclBindings :: [(Name, STy)], sDeclType :: STy, sDeclBody :: a }
  | SDType { sDeclPos :: Pos, sDeclName :: Name, sDeclType :: STy }
  | SEval a
  deriving (Show,Functor)

-- | AST de los términos. 
--   - info es información extra que puede llevar cada nodo. 
--       Por ahora solo la usamos para guardar posiciones en el código fuente.
--   - var es el tipo de la variables. Es 'Name' para fully named y 'Var' para locally closed. 
data Tm info var = 
    V info var
  | Const info Const
  | Lam info Name Ty (Tm info var)
  | App info (Tm info var) (Tm info var)
  | BinaryOp info BinaryOp (Tm info var) (Tm info var)
  | Fix info Name Ty Name Ty (Tm info var)
  | IfZ info (Tm info var) (Tm info var) (Tm info var)
  | Let info Name Ty (Tm info var) (Tm info var)        
  deriving (Functor)

instance (Show var) => Show (Tm info var) where
  show (V _ v)                 = show v
  show (Const _ c)             = show c
  show (Lam _ f ty tm)         = showFun [(f, ty)] tm 
    where showFun xs (Lam _ f ty tm') = showFun (xs ++ [(f,ty)]) tm'
          showFun xs tm = "Fun (" ++ concatMap (\ (f, ty) -> foldl1 (\x y -> x ++ ", " ++ y) f ++ ":" ++ show ty) xs'' ++ ") -> " ++ show tm
                      where xs' = groupBy (\a b -> snd a == snd b) xs
                            xs'' = map (\a -> (map fst a, snd (head a))) xs'
  show (App _ tm1 tm2)         = go tm1 ++ " " ++ go tm2 
    where go (V _ v)     = show v
          go (Const _ c) = show c
          go (App _ tm1 tm2) = go tm1 ++ " " ++ go tm2
          go t           = "(" ++ show t ++ ")"
  show (BinaryOp _ op tm1 tm2) = show op ++ " " ++ go tm1 ++ " " ++ go tm2
    where go (V _ v)     = show v
          go (Const _ c) = show c
          go t           = "(" ++ show t ++ ")"
  show (Fix _ f fty v vty tm)  = "Fix " ++ "(" ++ f ++ " : " ++ show fty ++ ")" ++ ") (" ++ v ++ " : " ++ show vty ++ ")" ++ " -> " ++ show tm
  show (IfZ _ tm1 tm2 tm3)     = "IfZ " ++ show tm1 ++ " then " ++ show tm2 ++ " else " ++ show tm3
  show (Let _ name ty tm1 tm2) = "Let " ++ name ++ " : " ++ show ty ++ " = " ++ show tm1 ++ " in " ++ show tm2

type NTerm = Tm Pos Name   -- ^ 'Tm' tiene 'Name's como variables ligadas y libres, guarda posición
type Term = Tm Pos Var     -- ^ 'Tm' con índices de De Bruijn como variables ligadas, different type of variables, guarda posición

data Var = 
    Bound !Int
  | Free Name

instance Show Var where
  show (Free v)  = v
  show (Bound n) = "(Bound " ++ show n ++ ")"

-- | AST de los términos con azúcar sintáctico. 
--   - info es información extra que puede llevar cada nodo. 
--   - var es el tipo de la variables. Es 'Name' para fully named y 'Var' para locally closed. 
data STm info var = 
    SV info var
  | SConst info Const
  | SLam info [(Name, STy)] (STm info var)
  | SApp info (STm info var) (STm info var)
  | SUnaryOp info UnaryOp (Maybe (STm info var))
  | SBinaryOp info BinaryOp (Maybe (STm info var)) (Maybe (STm info var))
  | SFix info Name STy Name STy (STm info var)
  | SIfZ info (STm info var) (STm info var) (STm info var)
  | SLet info Name [(Name, STy)] STy (STm info var) (STm info var)
  | SRec info Name [(Name, STy)] STy (STm info var) (STm info var)
  deriving (Show, Functor)

type SNTerm = STm Pos Name

-- | Obtiene la info en la raíz del término.
getInfo :: Tm info var -> info
getInfo (V i _) = i
getInfo (Const i _) = i
getInfo (Lam i _ _ _) = i
getInfo (App i _ _ ) = i
getInfo (BinaryOp i _ _ _) = i
getInfo (Fix i _ _ _ _ _) = i
getInfo (IfZ i _ _ _) = i
getInfo (Let i _ _ _ _) = i

-- | Obtiene las variables libres de un término.
freeVars :: Tm info Var -> [Name]
freeVars (V _ (Free v))       = [v]
freeVars (V _ _)              = []
freeVars (Lam _ _ _ t)        = freeVars t
freeVars (App _ l r)          = freeVars l ++ freeVars r
freeVars (BinaryOp _ _ t1 t2) = freeVars t1 ++ freeVars t2 
freeVars (Fix _ _ _ _ _ t)    = freeVars t
freeVars (IfZ _ c t e)        = freeVars c ++ freeVars t ++ freeVars e
freeVars (Const _ _)          = []
freeVars (Let _ _ _ t1 t2)    = freeVars t1 ++ freeVars t2
