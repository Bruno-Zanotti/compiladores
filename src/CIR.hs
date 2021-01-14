module CIR where

import Lang hiding (V)
import Data.List (intercalate, find)
import ClosureCompile as CC
import Data.Maybe (catMaybes, fromJust)
import Control.Monad.State

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

runCanon :: [IrDecl] -> CanonProg
runCanon decls = CanonProg (cp ++ [Left ("pcfmain", [], [("main", insts, Return res)])])
                where (cp, mb_insts) = unzip (runCanon' 0 decls)
                      insts = (concat . catMaybes) mb_insts
                      (Store _ (V res)) = last insts 

runCanon' :: Int -> [IrDecl] -> [(Either CanonFun CanonVal, Maybe [Inst])]
runCanon' s (IrVal n irtm : xs) = (Right n, Just (inst' ++ [Store n (V val)])) : runCanon' s' xs
                                where ((_, inst', Return val),s') = runState (blockConvert irtm) s
runCanon' s (IrFun n ns irtm: xs) = (Left (n, ns, [bb]), Nothing) : runCanon' s' xs
                                where (bb,s') = runState (blockConvert irtm) s
runCanon' _ [] = []



blockConvert :: IrTm -> State Int BasicBlock
blockConvert (IrVar v)             = return ("Var" ++ v, [], Return (G v))
blockConvert (CC.IrAccess v n)     = do val <- (getTerminatorVal . blockConvert) v
                                        reg <- getRegister
                                        return ("IrAccess", [Assign reg (Access val n)], Return (R reg))
blockConvert (IrCall f xs)         = do reg <- getRegister
                                        val <- (getTerminatorVal . blockConvert) f
                                        let fun = do getTerminatorVal . blockConvert
                                        vals <- mapM fun xs
                                        return ("Call", [Assign reg (Call val vals)], Return (R reg))
blockConvert (IrConst (CNat n))    = return ("Const", [], Return (C n))
blockConvert (IrBinaryOp op t1 t2) = do v1 <- (getTerminatorVal . blockConvert) t1
                                        v2 <- (getTerminatorVal . blockConvert) t2
                                        r1 <- getRegister
                                        r2 <- getRegister
                                        r3 <- getRegister
                                        return ("BinaryOp", [Assign r1 (V v1),
                                                             Assign r2 (V v2),
                                                             Assign r3 (BinOp op (R r1) (R r2))], Return (R r3))
blockConvert (CC.MkClosure v xs)   = do reg <- getRegister
                                        vals <- mapM (getTerminatorVal . blockConvert) xs
                                        return ("MkClosure", [Assign reg (CIR.MkClosure v vals)], Return (R reg))
blockConvert _ = undefined 
-- blockConvert (IrLet v t1 t2)       = undefined
-- blockConvert (IrIfZ c t f)         = undefined


getTerminatorVal :: State Int BasicBlock -> State Int Val
getTerminatorVal t1 = do s <- get
                         let ((_, _, Return val), s') = runState t1 s
                         put s'
                         return val

getRegister :: State Int Reg
getRegister = do s <- get
                 put (s+1)
                 return (Temp ("R" ++ show s))
