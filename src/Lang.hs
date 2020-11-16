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
  deriving Show

data UnaryOp = Succ | Pred
  deriving Show

data BinaryOp = Sum | Res
  deriving Show

-- | tipo de datos de declaraciones, parametrizado por el tipo del cuerpo de la declaración
data Decl a =
    Decl { declPos :: Pos, declName :: Name, declBody :: a }
  | Eval a
  deriving (Show,Functor)

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
  | UnaryOp info UnaryOp (Tm info var)
  | BinaryOp info BinaryOp (Tm info var) (Tm info var)
  | Fix info Name Ty Name Ty (Tm info var)
  | IfZ info (Tm info var) (Tm info var) (Tm info var)
  | Let info Name Ty (Tm info var) (Tm info var)
  deriving (Show, Functor)

type NTerm = Tm Pos Name   -- ^ 'Tm' tiene 'Name's como variables ligadas y libres, guarda posición
type Term = Tm Pos Var     -- ^ 'Tm' con índices de De Bruijn como variables ligadas, different type of variables, guarda posición

data Var = 
    Bound !Int
  | Free Name
  deriving Show

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
getInfo (UnaryOp i _ _) = i
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
freeVars (UnaryOp _ _ t)      = freeVars t
freeVars (BinaryOp _ _ t1 t2) = freeVars t1 ++ freeVars t2 
freeVars (Fix _ _ _ _ _ t)    = freeVars t
freeVars (IfZ _ c t e)        = freeVars c ++ freeVars t ++ freeVars e
freeVars (Const _ _)          = []
freeVars (Let _ _ _ t1 t2)    = freeVars t1 ++ freeVars t2
