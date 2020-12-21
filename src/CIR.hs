module CIR where

import Lang
import Data.List (intercalate)
import ClosureCompile as CC

newtype Reg = Temp String
  deriving Show

data Val = R Reg | C Int | G Name
  deriving Show

type Loc = String

data Inst =
    Assign Reg Expr
  | Store Name Expr
  deriving Show

data Expr =
    BinOp BinaryOp Val Val
  | UnOp UnaryOp Val
  | Phi [(Loc, Val)]
  | Call Val [Val]
  | MkClosure Loc [Val]
  | V Val
  | Access Val Int
  deriving Show

data Terminator =
    Jump Loc
  | CondJump Cond Loc Loc
  | Return Val
  deriving Show

data Cond =
    Eq Val Val
  deriving Show

type BasicBlock = (Loc, [Inst], Terminator)
type Blocks = [BasicBlock]

type CanonFun = (String, [String], [BasicBlock])
type CanonVal = String -- Sólo el nombre, tipo puntero siempre
newtype CanonProg = CanonProg [Either CanonFun CanonVal]

print :: (Blocks, [Inst], Val) -> String
print (bs, is, v) =
  concatMap printBlock bs ++ show is ++ "\n" ++ show v ++ "\n"

printBlock :: BasicBlock -> String
printBlock (loc, is, t) =
  loc ++ ":\n" ++
  concatMap (\i -> "  " ++ show i ++ "\n") is ++
  show t ++ "\n"

instance Show CanonProg where
  show (CanonProg prog) = concatMap pr1 prog where
    pr1 (Left (f, args, blocks)) =
      f ++ "(" ++ intercalate ", " args ++ ") {\n"
        ++ concatMap printBlock blocks ++ "}\n\n"

    pr1 (Right v) =
      "declare " ++ v ++ "\n\n"

runCanon :: IrDecl -> CanonProg
runCanon (IrVal n irtm)    = CanonProg [Right (n)]
runCanon (IrFun n ns irtm) = CanonProg [Left (n, ns, [blockConvert irtm])]

blockConvert :: IrTm -> BasicBlock
blockConvert (IrVar v)             = ("Var " ++ v, [], Return (G v))
-- blockConvert (IrCall v)         = (v, [], Return v)
blockConvert (IrConst (CNat n))    = ("Const", [], Return (C n))
-- blockConvert (IrBinaryOp op t1 t2) = ("BinaryOp", [], Return v)
blockConvert (IrLet v t1 t2)       = ("Let" ++ v, [Assign (Temp ("Reg: " ++ v)) (Phi [(loc, (G v))])], Return (G v))
                                    where (loc, inst, term) = blockConvert t1
-- blockConvert (IrIfZ c t f)         = (v, [], Return v)
-- blockConvert (CC.MkClosure v xs)   = (v, [], Return v)
-- blockConvert (CC.IrAccess v n)     = (v, [], Return v)

-- IrCall IrTm [IrTm]
-- IrConst Const
-- IrBinaryOp BinaryOp IrTm IrTm
-- IrLet Name IrTm IrTm
-- IrIfZ IrTm IrTm IrTm
-- MkClosure Name [IrTm]
-- IrAccess IrTm Int

-- #IrVal {irDeclName = "y", irDeclDef = IrBinaryOp Add (IrConst (CNat 2)) (IrVar "x")}

-- #IrFun {irDeclName = "__0", irDeclArgNames = ["__clo2","__y1"], irDeclBody = IrBinaryOp Add #(IrConst (CNat 1)) (IrVar "x")}
