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
import Optimizations
import Options.Applicative ( execParser, info, helper, (<**>), fullDesc, progDesc, header )
import Bytecompile ( bcRead, bcWrite, bytecompileModule, runBC ) 
import ClosureCompile ( runCC )
import Common ( dropExtension )
import System.Process ( system )
import Data.Text.Lazy.IO as TIO (writeFile)
import LLVM.Pretty
import CIR ( runCanon )
import InstSel ( codegen )
import LLVM.AST ( Module )
import Data.Maybe (catMaybes)

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
    go (Interactive,files) = do runPCF (runInputT defaultSettings (main' files)); return ()
    go (Typecheck, files)  = do err <- runPCF $ catchErrors $ mapFiles typeCheckFile files
                                case err of
                                  Left _ -> return()
                                  Right e -> case e of
                                               Nothing -> return()
                                               Just () -> putStrLn "El programa tipa correctamente"
                                return ()
    go (Bytecompile, files)    = do runPCF $ catchErrors $ mapFiles byteCompileFile files; return ()
    go (Closurecompile, files) = do runPCF $ catchErrors $ mapFiles (closureCompileFile False) files; return ()
    go (Optimized, files) = do runPCF $ catchErrors $ mapFiles (closureCompileFile True) files; return ()
    go (Run,files)             = do bytecode <- mapM bcRead files 
                                    runPCF $ catchErrors $ mapM runBC bytecode
                                    return ()
          
main' :: (MonadPCF m, MonadMask m) => [String] -> InputT m ()
main' args = do
        lift $ catchErrors $ mapFiles compileFile args
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
typeCheckFile :: MonadPCF m => FilePath -> m ()
typeCheckFile f = do
    decls <- openFile f
    snterm <- declsToTerm decls
    term <- elab snterm
    tc term []
    return ()

-- Bytecompile
byteCompileFile :: MonadPCF m => FilePath -> m ()
byteCompileFile f = do
    sDecls <- openFile f
    -- type check
    decls <- catMaybes <$> mapM desugarDecl sDecls
    let declTerms = map (\(Decl p n b) -> Decl p n (elab' b)) decls
    mapM_ tcDecl declTerms
    term <- declsToTerm sDecls
    bytecode <- bytecompileModule term
    let outputFile = dropExtension (reverse(dropWhile isSpace (reverse f))) ++ ".byte"
    printPCF ("Generando archivo compilado "++outputFile++"..."++show bytecode)
    liftIO $ bcWrite bytecode outputFile

-- Closurecompile
closureCompileFile :: MonadPCF m => Bool -> FilePath -> m ()
closureCompileFile optimized f = do
    sDecls <- openFile f
    decls <- catMaybes <$> mapM desugarDecl sDecls
    let declTerms = map (\(Decl p n b) -> Decl p n (elab' b)) decls
    mapM_ tcDecl declTerms
    mapM_ addDecl declTerms

    printPCF "\nDeclaraciones:\n"
    decls <- if optimized then optimization declTerms else return declTerms
    mapM_ (\x-> printPCF (">> " ++ show x)) decls
    let llvm = codegen (runCanon (runCC decls))
    liftIO $ TIO.writeFile "output.ll" (ppllvm llvm)
    liftIO $ system "clang -Wno-override-module output.ll src/runtime.c -lgc -o prog"
    liftIO $ system "./prog"
    return ()

mapFiles :: MonadPCF m => (FilePath -> m ()) -> [FilePath] -> m ()
mapFiles f []     = return ()
mapFiles f (x:xs) = do f x
                       mapFiles f xs

openFile :: MonadPCF m => FilePath -> m [SDecl SNTerm]
openFile f = do
    printPCF ("Abriendo "++f++"...")
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- liftIO $ catch (readFile filename)
               (\e -> do let err = show (e :: IOException)
                         hPutStr stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err ++"\n")
                         return "")
    parseIO filename program x

declsToTerm :: MonadPCF m => [SDecl SNTerm] -> m SNTerm
declsToTerm (SDLet p n bs ty b:xs) = case xs of
                                      [] -> return (SLet p n bs ty b (SV p n))
                                      _  -> do ts <- declsToTerm xs
                                               return (SLet p n bs ty b ts)
declsToTerm (SDRec p n bs ty b:xs) = case xs of
                                      [] -> return (SRec p n bs ty b (SV p n))
                                      _  -> do ts <- declsToTerm xs
                                               return (SRec p n bs ty b ts)
declsToTerm (SDType p n ty :xs) = declsToTerm xs
declsToTerm (x:_) = do failPCF $ "Declaración invalida "++ show x

------------------------------------------

compileFile ::  MonadPCF m => String -> m ()
compileFile f = do
    decls <- openFile f
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
        md <- desugarDecl d
        case md of
          Nothing -> return ()
          Just d' -> do let Decl p' x' b' = d'
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