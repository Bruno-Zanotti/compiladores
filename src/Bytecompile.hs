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
pattern SUM      = 8
pattern RES      = 9
pattern IFZ      = 10
pattern FIX      = 11
pattern STOP     = 12
pattern JUMP     = 13
pattern SHIFT    = 14
pattern DROP     = 15
pattern PRINT    = 16
pattern TAILCALL = 17

bc :: MonadPCF m => Term -> m Bytecode
bc (V _ (Bound n))         = return [ACCESS, n]
bc (Const _ (CNat n))      = return [CONST, n]
bc (Lam _ _ _ t)           = do bt <- bt t
                                return ([FUNCTION, length bt] ++ bt)
bc (App _ f e)             = do btf <- bc f
                                bte <- bc e
                                return (btf ++ bte ++ [CALL])
bc (BinaryOp _ op t1 t2)  = do bt1 <- bc t1
                               bt2 <- bc t2
                               case op of
                                 Sum -> return (bt1 ++ bt2 ++ [SUM]) 
                                 Res -> return (bt1 ++ bt2 ++ [RES])
bc (Fix _ _ _ _ _ t)       = do bt <- bc t
                                return ([FUNCTION, length bt + 1] ++ bt ++ [RETURN, FIX])
bc (IfZ _ c t f)           = do btc <- bc c
                                btt <- bc t
                                btf <- bc f
                                return (btc ++ [IFZ, length btt + 2] ++ btt ++ [JUMP, length btf] ++ btf )
bc (Let _ _ _ t1 t2)       = do bt1 <- bc t1
                                bt2 <- bc t2
                                return (bt1 ++ [SHIFT] ++ bt2 ++ [DROP])

bt :: MonadPCF m => Term -> m Bytecode
bt (App _ f e)             = do btf <- bc f
                                bte <- bc e
                                return (btf ++ bte ++ [TAILCALL])
bt (IfZ _ c t f)           = do btc <- bc c
                                btt <- bt t
                                btf <- bt f
                                return (btc ++ [IFZ, length btt] ++ btt ++ btf)
bt (Let _ _ _ t1 t2)       = do bt1 <- bc t1
                                bt2 <- bt t2
                                return (bt1 ++ [SHIFT] ++ bt2)
bt t                       = do bt <- bc t
                                return (bt ++ [RETURN])

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
runBC' (CONST: n: cs) e s                               = runBC' cs e (I n:s)
runBC' (SUM: cs) e (I n1: I n2: s)                      = runBC' cs e (I (n2+n1):s)
runBC' (RES: cs) e (I n1: I n2: s)                      = runBC' cs e (I (max 0 (n2-n1)):s)
runBC' (ACCESS: i: cs) e s                              = runBC' cs e (e!!i:s)
runBC' (CALL: cs) e (v: (Fun ef cf): s)                 = runBC' cf (v:ef) (RA e cs:s)
runBC' (FUNCTION: l: cs) e s                            = case drop l cs of
                                                            FIX:cs' -> runBC' cs' e (Fun efix cf :s)
                                                            cs'     -> runBC' cs' e (Fun e cf:s)
                                                          where cf   = take l cs
                                                                efix = Fun efix cf : e
runBC' (RETURN: _) _  (v: (RA e c): s)                  = runBC' c e (v:s)
runBC' (IFZ: n: cs) e (c:s)                             = case c of
                                                            I 0 -> runBC' cs e s
                                                            _   -> runBC' ([JUMP, n] ++ cs) e s
runBC' [STOP] _ _                                       = return ()
runBC' (JUMP: n: cs) e s                                = runBC' (drop n cs) e s 
runBC' (SHIFT: cs) e (v:s)                              = runBC' cs (v:e) s
runBC' (DROP: cs) (_:e) s                               = runBC' cs e s
runBC' (PRINT: cs) e (n:s)                              = do printPCF ("El valor en el stack es: " ++ show n)
                                                             runBC' cs e (n:s)
runBC' (TAILCALL: _) _ (v: (Fun ef cf): ra@(RA _ _): s) = runBC' cf (v:ef) (ra: s)
runBC' cs _ _                                           = do failPCF ("Error en Ejecución a Bytecode procesando la instrucción " ++ show cs)
