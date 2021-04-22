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
                where ((cp,_), blocks) =  runWriter (runStateT (runCanon' decls) (0, "main", []))

runCanon' :: [IrDecl] -> StateT (Int, Loc, [Inst]) (Writer [BasicBlock]) [Either CanonFun CanonVal]
runCanon' (IrVal n irtm : xs) = do val <- blockConvert irtm
                                   (_, l, i) <- get
                                   case xs of
                                     [] -> do tell [(l, i ++ [Store n (V val)], Return val)]
                                              return [Right n]
                                     _  -> do putInstruction (Store n (V val))
                                              cps <- runCanon' xs
                                              return (Right n : cps)
runCanon' (IrFun n ns irtm: xs) = do (s, l, i) <- get
                                     let ((val, (s', loc, inst)), bbs) = runWriter (runStateT (blockConvert irtm) (s, "init", []))
                                     put (s', l, i)
                                     let last_block = (loc, inst, Return val)
                                     cps <- runCanon' xs
                                     return (Left (n, ns, bbs++[last_block]): cps)
runCanon' [] = return []

blockConvert :: IrTm -> StateT (Int, Loc, [Inst]) (Writer [BasicBlock]) Val
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
                                        putInstruction (Assign r1 (V v1))
                                        putInstruction (Assign r2 (V v2))
                                        putInstruction (Assign r3 (BinOp op (R r1) (R r2)))
                                        return (R r3)
blockConvert (CC.MkClosure v xs)   = do reg <- getRegister
                                        vals <- mapM blockConvert xs
                                        putInstruction (Assign reg (CIR.MkClosure v vals))
                                        return (R reg)
blockConvert (IrIfZ c t f)         = do cond     <- getLoc "cond"
                                        then_loc <- getLoc "then"
                                        else_loc <- getLoc "else"
                                        if_cont  <- getLoc "ifcont"
                                        rt  <- getRegister
                                        rf  <- getRegister
                                        ret <- getRegister
                                        endBlock cond (Jump cond)
                                        -- Bloque Cond
                                        vc <- blockConvert c
                                        endBlock then_loc (CondJump (Eq (C 0) vc) then_loc else_loc)
                                        -- Bloque Then
                                        vt <- blockConvert t
                                        (_, fromThen, _) <- get
                                        putInstruction (Assign rt (V vt))
                                        endBlock else_loc (Jump if_cont)
                                        -- Bloque Else 
                                        vf <- blockConvert f
                                        (_, fromElse, _) <- get
                                        putInstruction (Assign rf (V vf))
                                        endBlock if_cont (Jump if_cont)
                                        -- Bloque If Cont
                                        putInstruction (Assign ret (Phi [(fromThen, R rt), (fromElse, R rf)]))
                                        return (R ret)
blockConvert (IrLet v t1 t2)       = do vt1 <- blockConvert t1
                                        r1 <- getRegister
                                        putInstruction (Assign (Temp v) (V vt1))
                                        blockConvert t2

-- Funciones auxiliares --
getRegister :: Monad m => StateT (Int, Loc, [Inst]) m Reg
getRegister = do (s, loc, insts) <- get
                 put (s+1, loc, insts)
                 return (Temp ("R" ++ show s))

getLoc :: Monad m => Loc -> StateT (Int, Loc, [Inst]) m Loc
getLoc loc = do (s, l, i) <- get
                put (s+1, l, i)
                return (loc ++ "_" ++ show s)

putInstruction :: Monad m => Inst -> StateT (Int, Loc, [Inst]) m ()
putInstruction new_inst = modify (\(n, loc, inst) -> (n, loc, inst++[new_inst]))

endBlock :: Loc -> Terminator -> StateT (Int, Loc, [Inst]) (Writer [BasicBlock]) ()
endBlock new_loc term = do (s, loc, inst) <- get
                           tell [(loc, inst, term)]
                           put (s, new_loc, [])
