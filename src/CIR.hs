module CIR where

import Lang hiding (V)
import Data.List (intercalate, isPrefixOf)
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
runCanon decls = CanonProg (cp ++ [Left ("pcfmain", [], blocks)])
                where ((cp,_), blocks) =  runWriter (runStateT (runCanon' decls) (0, newBlock "main"))

runCanon' :: [IrDecl] -> StateT (Int, BasicBlock) (Writer [BasicBlock]) [Either CanonFun CanonVal]
runCanon' (IrVal n irtm : xs) = do val <- blockConvert irtm
                                   (_, (l, i, _)) <- get
                                   case xs of
                                     [] -> do tell [(l, i ++ [Store n (V val)], Return val)]
                                              return [Right n]
                                     _  -> do putInstruction (Store n (V val))
                                              cps <- runCanon' xs
                                              return (Right n : cps)
runCanon' (IrFun n ns irtm: xs) = do let ((val, (s, (loc, inst, _))), bbs) = runWriter (runStateT (blockConvert irtm) (0, newBlock "init"))
                                     let last_block = (loc, inst, Return val)
                                     cps <- runCanon' xs
                                     return (Left (n, ns, bbs++[last_block]): cps)
runCanon' [] = return []

blockConvert :: IrTm -> StateT (Int, BasicBlock) (Writer [BasicBlock]) Val
blockConvert (IrVar v)             = if "__" `isPrefixOf` v
                                          then return (R (Temp v))
                                          else return (G v)
blockConvert (CC.IrAccess f n)     = do val <- blockConvert f
                                        reg <- getRegister
                                        putInstruction (Assign reg (Access val n))
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
                                        loc <- getLoc (show op)
                                        -- endBlock (Jump loc)
                                        -- startBlock loc
                                        putInstruction (Assign r1 (V v1))
                                        putInstruction (Assign r2 (V v2))
                                        putInstruction (Assign r3 (BinOp op (R r1) (R r2)))
                                        return (R r3)
blockConvert (CC.MkClosure v xs)   = do reg <- getRegister
                                        vals <- mapM blockConvert xs
                                        putInstruction (Assign reg (CIR.MkClosure v vals))
                                        return (R reg)
blockConvert (IrIfZ c t f)         = do reg <- getRegister
                                        cond <- getLoc "cond"
                                        then_loc <- getLoc "then"
                                        else_loc <- getLoc "else"
                                        if_cont <- getLoc "ifcont"
                                        rc <- getRegister
                                        rt <- getRegister
                                        rf <- getRegister
                                        endBlock (Jump cond)
                                        startBlock cond
                                        vc <- blockConvert c
                                        putInstruction (Assign rc (V vc))
                                        endBlock (CondJump (Eq (C 0) vc) then_loc else_loc)
                                        startBlock then_loc
                                        vt <- blockConvert t
                                        putInstruction (Assign rt (V vt))
                                        endBlock (Jump if_cont)
                                        startBlock else_loc
                                        vf <- blockConvert f
                                        putInstruction (Assign rf (V vf))
                                        endBlock (Jump if_cont)
                                        startBlock if_cont
                                        putInstruction (Assign reg (Phi [(then_loc, R rt), (else_loc, R rf)]))
                                        return (R reg)
blockConvert (IrLet v t1 t2)       = do vt1 <- blockConvert t1
                                        loc <- getLoc v
                                        -- endBlock (Jump loc)
                                        -- startBlock loc
                                        r1 <- getRegister
                                        putInstruction (Assign (Temp v) (V vt1))
                                        blockConvert t2
                                        
-- Funciones auxiliares --

getRegister :: Monad m => StateT (Int, BasicBlock) m Reg
getRegister = do (s, bb) <- get
                 put (s+1, bb)
                 return (Temp ("R" ++ show s))

getLoc :: Monad m => Loc -> StateT (Int, BasicBlock) m Loc
getLoc loc = do (s, bb) <- get
                put (s+1, bb)
                return (loc ++ "_" ++ show s)

putInstruction :: Monad m => Inst -> StateT (Int, BasicBlock) m ()
putInstruction new_inst = modify (\(n, (loc, inst, ter)) -> (n, (loc, inst++[new_inst], ter)))

endBlock :: Terminator -> StateT (Int, BasicBlock) (Writer [BasicBlock]) ()
endBlock term = do (s, (loc, inst, _)) <- get
                   put (s, (loc, inst, term))
                   tell [(loc, inst, term)]

startBlock :: Loc -> StateT (Int, BasicBlock) (Writer [BasicBlock]) ()
startBlock new_loc = do modify (\(s, (_,_,_)) -> (s, newBlock new_loc))

newBlock :: Loc -> BasicBlock
newBlock loc = (loc, [], Return (C 0))
