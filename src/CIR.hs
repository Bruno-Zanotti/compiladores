module CIR where

import Lang hiding (V)
import Data.List (intercalate, find)
import ClosureCompile as CC
import Data.Maybe (catMaybes, fromJust)
import Control.Monad.State
import Control.Monad.Writer

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
runCanon decls = CanonProg (cp ++ [Left ("pcfmain", [], blocks ++ [("main", inst, Return res)])])
                where (cp, blocks', inst') =  unzip3 (runCanon' 0 [] decls)
                      blocks = concat blocks'
                      inst = concat inst'
                      (Store _ (V res)) = last inst

runCanon' :: Int -> [Inst] -> [IrDecl] -> [(Either CanonFun CanonVal, [BasicBlock], [Inst])]
runCanon' s is (IrVal n irtm : xs) = (Right n, bbs, inst) : runCanon' s' [] xs
                                where ((val, (s', inst')), bbs) = runWriter (runStateT (blockConvert irtm) (s, is))
                                      inst = inst' ++ [Store n (V val)]
runCanon' s is (IrFun n ns irtm: xs) = (Left (n, ns, bbs), [], []) : runCanon' s' [] xs
                                where ((_, (s', inst')), bbs) = runWriter (runStateT (blockConvert irtm) (s, is))
runCanon' _ _ [] = []


blockConvert :: IrTm -> StateT (Int, [Inst]) (Writer [BasicBlock]) Val
blockConvert (IrVar v)             = do reg <- getRegister
                                        -- tell [("Var " ++ v, [Assign reg (V (G v))], Return (R reg))]
                                        return (G v)
blockConvert (CC.IrAccess v n)     = do val <- blockConvert v
                                        -- let val = getReturnVal bbs 
                                        reg <- getRegister
                                        putInstruction (Assign reg (Access val n))
                                        -- tell [("IrAccess", [Assign reg (Access val n)], Return (R reg))]
                                        return (R reg)
blockConvert (IrCall f xs)         = do reg <- getRegister
                                        fun <- blockConvert f
                                        args <- mapM blockConvert xs
                                        putInstruction (Assign reg (Call fun args))
                                        return (R reg)
blockConvert (IrConst (CNat n))    = return (C n)
blockConvert (IrBinaryOp op t1 t2) = do v1 <- blockConvert t1
                                        v2 <- blockConvert t2
                                        r1 <- getRegister
                                        r2 <- getRegister
                                        r3 <- getRegister
                                        putInstruction (Assign r1 (V v1))
                                        putInstruction (Assign r2 (V v2))
                                        putInstruction (Assign r3 (BinOp op (R r1) (R r2)))
                                        -- tell [("BinaryOp", [Assign r1 (V v1),
                                        --                     Assign r2 (V v2),
                                        --                     Assign r3 (BinOp op (R r1) (R r2))], Return (R r3))]
                                        return (R r3)
blockConvert (CC.MkClosure v xs)   = do reg <- getRegister
                                        vals <- mapM blockConvert xs
                                        -- let vals = map getReturnVal bbvals
                                        putInstruction (Assign reg (CIR.MkClosure v vals))
                                        return (R reg)
                                        -- return (concat bbvals ++ [("MkClosure", [Assign reg (CIR.MkClosure v vals)], Return (R reg))])
blockConvert (IrIfZ c t f)         = do vc <- blockConvert c
                                        vt <- blockConvert t
                                        vf <- blockConvert f
                                        rc <- getRegister
                                        rt <- getRegister
                                        rf <- getRegister
                                        reg <- getRegister
                                        let cond  = ("cond", [Assign rc (V vc)], CondJump (Eq (C 0) vc) "then" "else")
                                        let then' = ("then", [Assign rt (V vt)], Jump "ifcont")
                                        let else' = ("else", [Assign rf (V vf)], Jump "ifcont")
                                        let ifcont = ("ifcont", [], Return (R reg))
                                        putInstruction (Assign reg (Phi [("then", vt), ("else", vf)]))
                                        tell [cond, then', else', ifcont]
                                        return (R reg)
                                        -- return (cond ++ then' ++ else' ++ [("ifcont", [Assign reg (Phi [("then", vt), ("else", vf)])], Return (R reg))])
blockConvert _ = undefined 
-- blockConvert (IrLet v t1 t2)       = undefined


getTerminatorVal :: State Int [BasicBlock] -> State Int Val
getTerminatorVal t1 = do s <- get
                         let (bbs, s') = runState t1 s
                         let val = getReturnVal bbs
                         put s'
                         return val

getReturnVal :: [BasicBlock] -> Val
getReturnVal bb = val
                where (_, _, Return val) = last bb
                  

getRegister :: Monad m => StateT (Int, [Inst]) m Reg
getRegister = do (s, inst) <- get
                 put (s+1, inst)
                 return (Temp ("R" ++ show s))

putInstruction :: Monad m => Inst -> StateT (Int, [Inst]) m ()
putInstruction new_inst = modify (\(n, inst) -> (n, inst++[new_inst]))