{-# LANGUAGE RecordWildCards #-}

{-|
Module      : Main
Description : Compilador de PCF.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Main where

import System.Console.Haskeline ( defaultSettings, getInputLine, runInputT, InputT )
import Control.Monad.Catch (MonadMask)

--import Control.Monad
import Control.Monad.Trans
import Data.List (nub,  intersperse, isPrefixOf )
import Data.Char ( isSpace )
import Control.Exception ( catch , IOException )
import System.Environment ( getArgs )
import System.IO ( stderr, hPutStr )

import Global ( GlEnv(..) )
import Errors
import Lang
import Parse ( P, stm, program, declOrSTm, runP, Mode(..), parseArgs )
import Elab ( elab, desugarDecl, elab', desugarTy )
-- import Eval ( eval )
import CEK ( eval )
import PPrint ( pp , ppTy )
import MonadPCF
    ( when,
      MonadState(get, put),
      MonadError(throwError),
      MonadPCF,
      addDecl,
      addTy,
      catchErrors,
      failPCF,
      lookupDecl,
      printPCF,
      runPCF,
      modify )
import TypeChecker ( tc, tcDecl )
import Options.Applicative ( execParser, info, helper, (<**>), fullDesc, progDesc, header )
import Bytecompile ( bcRead, bcWrite, bytecompileModule, runBC ) 
import ClosureCompile ( runCC )
import Common ( dropExtension )
import System.Process ( system )
import Data.Text.Lazy.IO as TIO (writeFile)
-- import qualified Data.ByteString.Lazy as TIO (writeFile)
import LLVM.Pretty
import CIR ( runCanon )
import InstSel ( codegen )
import LLVM.AST ( Module )

prompt :: String
prompt = "PCF> "

main :: IO ()
main = execParser opts >>= go
  where 
    opts = info (parseArgs <**> helper) 
           (fullDesc 
           <> progDesc "Compilador de PCF" 
           <> header "Compilador de PCF de la materia Compiladores 2020")
    go :: (Mode,[FilePath]) -> IO ()
    go (Interactive,files) =
        do runPCF (runInputT defaultSettings (main' files))
           return ()
    go (Typecheck, files) = do err <- runPCF $ catchErrors $ typeCheckFiles files
                               case err of
                                 Left _ -> return()
                                 Right e -> case e of
                                              Nothing -> return()
                                              Just () -> putStrLn "El programa tipa correctamente"
                               return ()
    go (Bytecompile, files) = do runPCF $ catchErrors $ byteCompileFiles files
                                 return ()
    go (Closurecompile, files) = do runPCF $ catchErrors $ closureCompileFiles files
                                    -- let llvm = "323"
                                    -- let commandline = "clang -Wno-override-module output.ll runtime.c -lgc -o prog"
                                    -- liftIO $ TIO.writeFile "output.ll" (ppllvm llvm)
                                    -- liftIO $ system commandline
                                    return ()
    go (Run,files) = do
      bytecode <- mapM bcRead files 
      runPCF $ catchErrors $ mapM runBC bytecode
      return ()
          
main' :: (MonadPCF m, MonadMask m) => [String] -> InputT m ()
main' args = do
        lift $ catchErrors $ compileFiles args
        s <- lift get
        when (inter s) $ liftIO $ putStrLn
          (  "Entorno interactivo para PCF0.\n"
          ++ "Escriba :? para recibir ayuda.")
        loop  
  where loop = do
           minput <- getInputLine prompt
           case minput of
               Nothing -> return ()
               Just "" -> loop
               Just x -> do
                       c <- liftIO $ interpretCommand x
                       b <- lift $ catchErrors $ handleCommand c
                       maybe loop (flip when loop) b

------------------------------------------
--                Modes                 --
------------------------------------------

-- Typecheck
typeCheckFiles :: MonadPCF m => [FilePath] -> m ()
typeCheckFiles []     = return ()
typeCheckFiles (x:xs) = do
        typeCheckFile x
        typeCheckFiles xs

typeCheckFile :: MonadPCF m => FilePath -> m ()
typeCheckFile f = do
    printPCF ("Abriendo "++f++"...")
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- liftIO $ catch (readFile filename)
               (\e -> do let err = show (e :: IOException)
                         hPutStr stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err ++"\n")
                         return "")
    decls <- parseIO filename program x
    snterm <- declsToTerm decls
    term <- elab snterm
    tc term []
    return ()

-- Bytecompile
byteCompileFiles :: MonadPCF m => [FilePath] -> m ()
byteCompileFiles []     = return ()
byteCompileFiles (x:xs) = do
        byteCompileFile x
        byteCompileFiles xs

-- TODO: unificar con funcion CompileFile
byteCompileFile :: MonadPCF m => FilePath -> m ()
byteCompileFile f = do
    printPCF ("Abriendo "++f++"...")
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- liftIO $ catch (readFile filename)
               (\e -> do let err = show (e :: IOException)
                         hPutStr stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err ++"\n")
                         return "")
    decls <- parseIO filename program x
    mapM_ handleDecl decls
    term <- declsToTerm decls
    bytecode <- bytecompileModule term
    let outputFile = dropExtension filename ++ ".byte"
    printPCF ("Generando archivo compilado "++outputFile++"..."++show bytecode)
    liftIO $ bcWrite bytecode outputFile

-- Closurecompile
closureCompileFiles :: MonadPCF m => [FilePath] -> m ()
closureCompileFiles []     = return ()
closureCompileFiles (x:xs) = do
        closureCompileFile x
        closureCompileFiles xs

closureCompileFile :: MonadPCF m => FilePath -> m ()
closureCompileFile f = do
    printPCF ("Abriendo "++f++"...")
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- liftIO $ catch (readFile filename)
               (\e -> do let err = show (e :: IOException)
                         hPutStr stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err ++"\n")
                         return "")
    sDecls <- parseIO filename program x
    mapM_ handleDecl sDecls
    decls <- mapM desugarDecl sDecls
    let declTerms = map (\(Decl p n b) -> Decl p n (elab' b)) decls
    -- TODO: borrar print
    printPCF ("Declaraciones pre CC\n" ++ show declTerms)
    mapM_ (\x-> printPCF (">> " ++ show x)) (runCC declTerms)
    printPCF (show (runCanon (runCC declTerms)))
    let llvm = codegen (runCanon (runCC declTerms))
    let commandline = "clang -Wno-override-module output.ll src/runtime.c -lgc -o prog"
    liftIO $ TIO.writeFile "output.ll" (ppllvm llvm)
    liftIO $ system commandline
    liftIO $ system "./prog"
    return ()


declsToTerm :: MonadPCF m => [SDecl SNTerm] -> m SNTerm
declsToTerm (SDLet p n bs ty b:xs) = case xs of
                                      [] -> return (SLet p n bs ty b (SV p n))
                                      _  -> do ts <- declsToTerm xs
                                               return (SLet p n bs ty b ts)
declsToTerm (SDRec p n bs ty b:xs) = case xs of
                                      [] -> return (SRec p n bs ty b (SV p n))
                                      _  -> do ts <- declsToTerm xs
                                               return (SRec p n bs ty b ts)
declsToTerm (x:_) = do failPCF $ "Declaración invalida "++ show x

------------------------------------------

compileFiles ::  MonadPCF m => [String] -> m ()
compileFiles []     = return ()
compileFiles (x:xs) = do
        modify (\s -> s { lfile = x, inter = False })
        compileFile x
        compileFiles xs

compileFile ::  MonadPCF m => String -> m ()
compileFile f = do
    printPCF ("Abriendo "++f++"...")
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- liftIO $ catch (readFile filename)
               (\e -> do let err = show (e :: IOException)
                         hPutStr stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err ++"\n")
                         return "")
    decls <- parseIO filename program x
    mapM_ handleDecl decls

parseIO ::  MonadPCF m => String -> P a -> String -> m a
parseIO filename p x = case runP p x filename of
                  Left e  -> throwError (ParseErr e)
                  Right r -> return r

handleDecl ::  MonadPCF m => SDecl SNTerm -> m ()
handleDecl (SDType _ n sty) = do 
                        ty <- desugarTy sty
                        addTy n ty
handleDecl d = do
        d' <- desugarDecl d
        let Decl p' x' b' = d'
        let tt = elab' b'
        tcDecl (Decl p' x' tt)
        te <- eval tt
        addDecl (Decl p' x' te)

data Command = Compile CompileForm
             | Print String
             | Type String
             | Browse
             | Quit
             | Help
             | Noop

data CompileForm = CompileInteractive  String
                 | CompileFile         String

data InteractiveCommand = Cmd [String] String (String -> Command) String

-- | Parser simple de comando interactivos
interpretCommand :: String -> IO Command
interpretCommand x
  =  if isPrefixOf ":" x then
       do  let  (cmd,t')  =  break isSpace x
                t         =  dropWhile isSpace t'
           --  find matching commands
           let  matching  =  filter (\ (Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
           case matching of
             []  ->  do  putStrLn ("Comando desconocido `" ++ cmd ++ "'. Escriba :? para recibir ayuda.")
                         return Noop
             [Cmd _ _ f _]
                 ->  do  return (f t)
             _   ->  do  putStrLn ("Comando ambigüo, podría ser " ++
                                   concat (intersperse ", " [ head cs | Cmd cs _ _ _ <- matching ]) ++ ".")
                         return Noop

     else
       return (Compile (CompileInteractive x))

commands :: [InteractiveCommand]
commands
  =  [ Cmd [":browse"]      ""        (const Browse) "Ver los nombres en scope",
       Cmd [":load"]        "<file>"  (Compile . CompileFile)
                                                     "Cargar un programa desde un archivo",
       Cmd [":print"]       "<exp>"   Print          "Imprime un término y sus ASTs sin evaluarlo",
       Cmd [":type"]        "<exp>"   Type           "Chequea el tipo de una expresión",
       Cmd [":quit",":Q"]        ""        (const Quit)   "Salir del intérprete",
       Cmd [":help",":?"]   ""        (const Help)   "Mostrar esta lista de comandos" ]

helpTxt :: [InteractiveCommand] -> String
helpTxt cs
  =  "Lista de comandos:  Cualquier comando puede ser abreviado a :c donde\n" ++
     "c es el primer caracter del nombre completo.\n\n" ++
     "<expr>                  evaluar la expresión\n" ++
     "let <var> = <expr>      definir una variable\n" ++
     unlines (map (\ (Cmd c a _ d) ->
                   let  ct = concat (intersperse ", " (map (++ if null a then "" else " " ++ a) c))
                   in   ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d) cs)

-- | 'handleCommand' interpreta un comando y devuelve un booleano
-- indicando si se debe salir del programa o no.
handleCommand ::  MonadPCF m => Command  -> m Bool
handleCommand cmd = do
   s@GlEnv {..} <- get
   case cmd of
       Quit   ->  return False
       Noop   ->  return True
       Help   ->  printPCF (helpTxt commands) >> return True
       Browse ->  do  printPCF (unlines [ s | s <- reverse (nub (map declName glb)) ])
                      return True
       Compile c ->
                  do  case c of
                          CompileInteractive e -> compilePhrase e
                          CompileFile f        -> put (s {lfile=f}) >> compileFile f
                      return True
       Print e   -> printPhrase e >> return True
       Type e    -> typeCheckPhrase e >> return True

compilePhrase ::  MonadPCF m => String -> m ()
compilePhrase x =
  do
    dot <- parseIO "<interactive>" declOrSTm x
    case dot of 
      Left d  -> handleDecl d
      Right t -> handleTerm t

handleTerm ::  MonadPCF m => SNTerm -> m ()
handleTerm t = do
         tt <- elab t
         s <- get
         ty <- tc tt (tyEnv s)
         te <- eval tt
         printPCF (pp te ++ " : " ++ ppTy ty)

printPhrase   :: MonadPCF m => String -> m ()
printPhrase x =
  do
    x' <- parseIO "<interactive>" stm x
    ex <- elab x'
    t  <- case x' of 
           (SV _ f) -> maybe ex id <$> lookupDecl f
           _        -> return ex  
    printPCF "NTerm:"
    printPCF (show x')
    printPCF "\nTerm:"
    printPCF (show t)

typeCheckPhrase :: MonadPCF m => String -> m ()
typeCheckPhrase x = do
         t <- parseIO "<interactive>" stm x
         tt <- elab t
         s <- get
         ty <- tc tt (tyEnv s)
         printPCF (ppTy ty)