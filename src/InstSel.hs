module InstSel where

import CIR
import Data.String
import Control.Monad.Writer
import Control.Monad.State
import qualified Lang
--import Common

import LLVM.AST
import LLVM.AST.Global
import qualified LLVM.AST.AddrSpace

import qualified LLVM.AST.Linkage as L
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.CallingConvention as CC
import qualified LLVM.AST.IntegerPredicate as IP

i1 :: Type
i1 = IntegerType 1

integer :: Type
integer = IntegerType 32

ptr :: Type
ptr = PointerType integer (LLVM.AST.AddrSpace.AddrSpace 0)

global :: Name -> Type -> Operand
global nm ty = ConstantOperand $ C.GlobalReference ty nm

ptrptr :: Type
ptrptr = PointerType ptr (LLVM.AST.AddrSpace.AddrSpace 0)

-- aridad 2, como todas por ahora
fun :: Type
fun = FunctionType ptr [ptr, ptr] False

fptr :: Type
fptr = PointerType fun (LLVM.AST.AddrSpace.AddrSpace 0)

mkclosureTy :: Type
mkclosureTy = PointerType (FunctionType ptr [fptr, integer] True) -- true -> vararg
                           (LLVM.AST.AddrSpace.AddrSpace 0)

printTy :: Type
printTy = PointerType (FunctionType integer [integer] False)
                           (LLVM.AST.AddrSpace.AddrSpace 0)

defnMkclosure :: Definition
defnMkclosure = GlobalDefinition $ functionDefaults {
    name = mkName "pcf_mkclosure"
  , parameters = ([Parameter fptr (mkName "f") [],
                   Parameter integer (mkName "nenv") []], True) -- true -> vararg
  , linkage = L.External
  , returnType = ptr
  }

defnPrint :: Definition
defnPrint = GlobalDefinition $ functionDefaults {
    name = mkName "pcf_print"
  , parameters = ([Parameter integer (mkName "x") []], False)
  , linkage = L.External
  , returnType = integer
  }

emptyModule :: Module
emptyModule =
  defaultModule {
      moduleName = fromString "pcfprog"
    , moduleDefinitions = [defnMkclosure, defnPrint]
  }

codegen :: CanonProg -> Module
codegen (CanonProg funs) =
  let defns = map (either cgFun cgVal) funs in
  let modulo = emptyModule in
  modulo {
      moduleDefinitions = moduleDefinitions modulo ++ defns
  }

cgFun :: CanonFun -> Definition
cgFun (f, args, blocks) =
  let comp = mapM cgBlock blocks in
  let (llvmBlocks, _) = runState comp 0 in
  GlobalDefinition $ functionDefaults {
      name        = Name (fromString f)
    , parameters  = ([Parameter ptr (mkName nm) [] | nm <- args], False)
    , basicBlocks = llvmBlocks
    , returnType  = ptr
  }

cgVal :: CanonVal -> Definition
cgVal nm =
  GlobalDefinition $ globalVariableDefaults {
      name = mkName nm
    , LLVM.AST.Global.type' = ptr
    , linkage = L.Internal
    , initializer = Just (C.Null ptr)
  }

cgBlock :: CIR.BasicBlock -> State Int LLVM.AST.BasicBlock
cgBlock (lab, insts, term) = do
  let comp = do mapM_ cgInst insts
                cgTerm term
  (t, is) <- runWriterT comp
  return $ BasicBlock (mkName lab) is t

type M a = WriterT [Named LLVM.AST.Instruction] (State Int) a

fresh :: M Int
fresh = do
  modify (+1)
  get

freshName' :: String -> M Name
freshName' s = do
  i <- fresh
  return (mkName (s ++ show i))

freshName :: M Name
freshName = freshName' "__r_"

cgInst :: CIR.Inst -> M ()
cgInst (Assign (Temp i) e) = do 
  ee <- cgExpr e
  tell [mkName i := ee]

cgInst (CIR.Store nm e) = do
  ee <- cgExpr e
  r <- freshName
  tell [r := ee,
        Do $ LLVM.AST.Store False (global (mkName nm) ptrptr)
                            (LocalReference ptr r)
                            Nothing 0 []]

cint :: Integral a => a -> Operand
cint i = ConstantOperand $ C.Int 32 (fromIntegral i)

zero :: Operand
zero = cint 0

one :: Operand
one = cint 1

cgExpr :: CIR.Expr -> M LLVM.AST.Instruction
-- FIXME: duplicación
cgExpr (BinOp Lang.Sum v1 v2) = do
  v1 <- cgV v1
  v2 <- cgV v2
  vf1 <- freshName
  vf2 <- freshName
  r <- freshName
  tell [vf1 := PtrToInt v1 integer []]
  tell [vf2 := PtrToInt v2 integer []]
  tell [r := Add False False
               (LocalReference integer vf1)
               (LocalReference integer vf2)
               []]
  return (IntToPtr (LocalReference integer r) ptr [])

cgExpr (BinOp Lang.Res v1 v2) = do
  v1 <- cgV v1
  v2 <- cgV v2
  vf1 <- freshName
  vf2 <- freshName
  r <- freshName
  tell [vf1 := PtrToInt v1 integer []]
  tell [vf2 := PtrToInt v2 integer []]
  tell [r := Sub False False
               (LocalReference integer vf1)
               (LocalReference integer vf2)
               []]
  return (IntToPtr (LocalReference integer r) ptr [])

-- cgExpr (BinOp Lang.Prod v1 v2) = do
--   v1 <- cgV v1
--   v2 <- cgV v2
--   vf1 <- freshName
--   vf2 <- freshName
--   r <- freshName
--   tell [vf1 := PtrToInt v1 integer []]
--   tell [vf2 := PtrToInt v2 integer []]
--   tell [r := Mul False False
--                (LocalReference integer vf1)
--                (LocalReference integer vf2)
--                []]
--   return (IntToPtr (LocalReference integer r) ptr [])

cgExpr (UnOp Lang.Succ v) = do
  cgExpr (BinOp Lang.Sum v (C 1)) -- trucho

cgExpr (UnOp Lang.Pred v) = do
  cgExpr (BinOp Lang.Res v (C 1)) -- trucho

-- cgExpr (UnOp Lang.Print v) = do
--   v <- cgV v
--   vf <- freshName
--   r <- freshName
--   tell [vf := PtrToInt v integer []]
--   tell [r := LLVM.AST.Call
--                  Nothing
--                  CC.C
--                  []
--                  (Right (global (mkName "pcf_print") printTy))
--                  [(LocalReference integer vf, [])]
--                  []
--                  []]
--   return (IntToPtr (LocalReference integer r) ptr [])

cgExpr (CIR.Phi brs) = do
  args <- mapM (\(loc, v) -> do op <- cgV v
                                return (op, mkName loc)) brs
  return $ LLVM.AST.Phi ptr args []

-- truchísimo
cgExpr (V v) = do
  cgExpr (BinOp Lang.Sum v (C 0))

cgExpr (CIR.Call v args) = do
 v <- cgV v
 f <- freshName' "fun"
 tell [f := BitCast v fptr []]
 args <- mapM (\av -> do a <- cgV av
                         return (a, [])) args
 return $
  LLVM.AST.Call
      Nothing
      CC.C
      []
      (Right (LocalReference fptr f))
      args
      []
      []

cgExpr (CIR.MkClosure fn args) = do
 let af = (global (mkName fn) fptr, [])
 let an = (cint (Prelude.length args), [])
 env_args <- mapM (\av -> do a <- cgV av
                             return (a, [])) args
 return $
  LLVM.AST.Call
      Nothing
      CC.C
      []
      (Right (global (mkName "pcf_mkclosure") mkclosureTy))
      (af : an : env_args)
      []
      []

cgExpr (Access v idx) = do
  tmp <- freshName' "addr"
  v <- cgV v
  r <- freshName
  tell [
    r := BitCast v ptrptr [],
    tmp := GetElementPtr False (LocalReference ptrptr r) [cint idx] []
    -- esto debe estar mal porque es un i32* ?
   ]
  return $ Load False (LocalReference ptrptr tmp) Nothing 0 []

cgV :: CIR.Val -> M LLVM.AST.Operand
cgV (R (Temp i)) =
  return $ LocalReference ptr (mkName i)

cgV (C i) = do
  n <- freshName
  tell [n := IntToPtr (cint i) ptr []]
  return $ LocalReference ptr n

cgV (G nm) = do
  r <- freshName
  tell [r := Load False (global (mkName nm) ptrptr)
                  Nothing 0 []]
  return $ LocalReference ptr r

cgTerm :: CIR.Terminator -> M (Named LLVM.AST.Terminator)
cgTerm (Jump l) =
  return $ Do $ Br (mkName l) []

cgTerm (CondJump (Eq v1 v2) lt lf) = do
  b <- freshName' "cond"
  v1 <- cgV v1
  v2 <- cgV v2
  tell [b := ICmp IP.EQ v1 v2 []]
  return $ Do $ CondBr (LocalReference i1 b) (mkName lt) (mkName lf) []

cgTerm (Return v1) = do
  v1 <- cgV v1
  return $ Do $ Ret (Just v1) []
