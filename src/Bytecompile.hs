{-# LANGUAGE PatternSynonyms #-}
{-|
Module      : Bytecompile
Description : Compila a bytecode. Ejecuta bytecode.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental
Este módulo permite compilar módulos a la BVM. También provee una implementación de la BVM 
para ejecutar bytecode.
-}
module Bytecompile
  (Bytecode, bytecompileModule, runBC, bcWrite, bcRead)
 where

import Lang 
import MonadPCF
import Elab (elab)

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word32, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord32le )
import Data.Binary.Get ( getWord32le, isEmpty )
type Bytecode = [Int]

newtype Bytecode32 = BC { un32 :: [Word32] }

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode32 where
  put (BC bs) = mapM_ putWord32le bs
  get = go 
    where go =  
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord32le
                      BC xs <- go
                      return $ BC (x:xs)

{- Estos sinónimos de patrón nos permiten escribir y hacer
pattern-matching sobre el nombre de la operación en lugar del código
entero, por ejemplo:
 
   f (CALL : cs) = ...
 Notar que si hubieramos escrito algo como
   call = 5
 no podríamos hacer pattern-matching con `call`.
 En lo posible, usar estos códigos exactos para poder ejectutar un
 mismo bytecode compilado en distintas implementaciones de la máquina.
-}
pattern RETURN   = 1
pattern CONST    = 2
pattern ACCESS   = 3
pattern FUNCTION = 4
pattern CALL     = 5
pattern SUCC     = 6
pattern PRED     = 7
pattern IFZ      = 8
pattern FIX      = 9
pattern STOP     = 10
pattern JUMP     = 11
pattern SHIFT    = 12
pattern DROP     = 13
pattern PRINT    = 14

bc :: MonadPCF m => Term -> m Bytecode
bc (V _ (Bound n))     = return [ACCESS, n]
bc (Const _ (CNat n))  = return [CONST, n]
bc (Lam _ _ _ t)       = do bt <- bc t
                            return ([FUNCTION, length bt + 1] ++ bt ++ [RETURN])
bc (App _ f e)         = do btf <- bc f
                            bte <- bc e
                            return (btf ++ bte ++ [CALL])
bc (UnaryOp _ Succ t)  = do bt <- bc t
                            return (bt ++ [SUCC]) 
bc (UnaryOp _ Pred t)  = do bt <- bc t
                            return (bt ++ [PRED])
bc (Fix _ _ _ _ _ t)   = do bt <- bc t
                            return ([FUNCTION, length bt + 1] ++ bt ++ [RETURN, FIX])
bc (IfZ _ c t f)       = do btc <- bc c
                            btt <- bc t
                            btf <- bc f
                            let args = [IFZ] ++ [JUMP, length btt + 2] ++ btt ++ [JUMP, length btf] ++ btf
                            return ([FUNCTION, length args + 1] ++ args ++ [RETURN] ++ btc ++ [CALL])
bc (Let _ _ _ t1 t2)  = do bt1 <- bc t1
                           bt2 <- bc t2
                           return (bt1 ++ [SHIFT] ++ bt2 ++ [DROP])

bytecompileModule :: MonadPCF m => SNTerm -> m Bytecode
bytecompileModule st = do t <- elab st 
                          byte <- bc t
                          return (byte ++ [PRINT, STOP])

-- | Toma un bytecode, lo codifica y lo escribe un archivo 
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)

---------------------------
-- * Ejecución de bytecode
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = (map fromIntegral . un32 <$> decode) <$> BS.readFile filename

data Val = 
    I Int 
  | Fun Env Bytecode
  | RA Env Bytecode
  deriving (Show)

type Stack = [Val]
type Env = [Val]

runBC :: MonadPCF m => Bytecode -> m ()
runBC cs = runBC' cs [] []

runBC' :: MonadPCF m => Bytecode -> Env -> Stack -> m ()
runBC' (CONST: n: cs) e s               = runBC' cs e (I n:s)
runBC' (SUCC: cs) e (I n: s)            = runBC' cs e (I (n+1):s)
runBC' (PRED: cs) e (I n: s)            = runBC' cs e (I (n-1):s)
runBC' (ACCESS: i: cs) e s              = runBC' cs e (e!!i:s)
runBC' (CALL: cs) e (v: (Fun ef cf): s) = runBC' cf (v:ef) (RA e cs:s)
runBC' (FUNCTION: l: cs) e s            = case drop l cs of
                                            FIX:cs' -> runBC' cs' e (Fun efix cf :s)
                                            cs'     -> runBC' cs' e (Fun e cf:s)
                                          where cf = take l cs
                                                efix = Fun efix cf : e
runBC' (RETURN: _) _  (v: (RA e c): s)  = runBC' c e (v:s)
runBC' (IFZ: cs@(JUMP: _: cs')) (c:e) s = case c of
                                I 0 -> runBC' cs' e s
                                _   -> runBC' cs e s
runBC' [STOP] _ _          = return ()
runBC' (JUMP: n: cs) e s    = runBC' (drop n cs) e s 
runBC' (SHIFT: cs) e (v:s) = runBC' cs (v:e) s
runBC' (DROP: cs) (_:e) s  = runBC' cs e s
runBC' (PRINT: cs) e (n:s) = do
                  printPCF ("El valor en el stack es: " ++ show n)
                  runBC' cs e (n:s)
runBC' _ _ _ = do failPCF "Error en Ejecución a Bytecode "
