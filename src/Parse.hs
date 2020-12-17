{-# LANGUAGE TupleSections #-}
{-|
Module      : Parse
Description : Define un parser de términos PCF0 a términos fully named.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Parse (stm, Parse.parse, decl, runP, P, program, declOrSTm, Mode(..), parseArgs ) where

import Prelude hiding ( const )
import Lang
import Common
import Text.Parsec hiding (runP)
import qualified Text.Parsec.Token as Tok
import Text.ParserCombinators.Parsec.Language ( GenLanguageDef(..), emptyDef )
import qualified Options.Applicative as OptApp ( flag', flag, Parser, short, long, many, metavar, help, str, argument, (<|>) ) 

type P = Parsec String ()

-----------------------
-- Lexer
-----------------------
-- | Analizador de Tokens
lexer :: Tok.TokenParser u
lexer = Tok.makeTokenParser $
        emptyDef {
         commentLine    = "#",
         reservedNames = ["let", "in", "rec", "fun", "fix", "then", "else", "succ", "pred", "ifz", "Nat", "type", "sum", "res"],
         reservedOpNames = ["->",":","="]
        }

whiteSpace :: P ()
whiteSpace = Tok.whiteSpace lexer

natural :: P Integer 
natural = Tok.natural lexer

parens :: P a -> P a
parens = Tok.parens lexer

identifier :: P String
identifier = Tok.identifier lexer

reserved :: String -> P ()
reserved = Tok.reserved lexer

reservedOp :: String -> P ()
reservedOp = Tok.reservedOp lexer

-----------------------
-- Parsers
-----------------------

num :: P Int
num = fromInteger <$> natural

var :: P Name
var = identifier

tyvar :: P Name
tyvar = Tok.lexeme lexer $ do
          c  <- try (lookAhead upper)
          cs <- option "" identifier
          return (c:cs)

getPos :: P Pos
getPos = do pos <- getPosition
            return $ Pos (sourceLine pos) (sourceColumn pos)

tyatom :: P STy
tyatom = (reserved "Nat" >> return SNatTy)
         <|> parens typeP
         <|> (SNamedTy <$> tyvar)

typeP :: P STy
typeP = try (do x <- tyatom
                reservedOp "->"
                SFunTy x <$> typeP)
      <|> tyatom 
          
const :: P Const
const = CNat <$> num

unaryOpName :: P UnaryOp
unaryOpName =
      (reserved "succ" >> return Succ)
  <|> (reserved "pred" >> return Pred)

unaryOp :: P SNTerm
unaryOp = try unaryOpApp <|> unaryOpNotApp

unaryOpApp :: P SNTerm
unaryOpApp = do i <- getPos
                o <- unaryOpName
                SUnaryOp i o . Just <$> atom

unaryOpNotApp :: P SNTerm
unaryOpNotApp = do
  i <- getPos
  o <- unaryOpName
  return (SUnaryOp i o Nothing)

binaryOpName :: P BinaryOp
binaryOpName =
      (reserved "sum" >> return Sum)
  <|> (reserved "res" >> return Res)

binaryOp :: P SNTerm
binaryOp = try binaryOpApp <|> binaryOpNotApp

binaryOpApp :: P SNTerm
binaryOpApp = do i <- getPos
                 o <- binaryOpName
                 t1 <- atom
                 SBinaryOp i o (Just t1) . Just <$> atom

binaryOpNotApp :: P SNTerm
binaryOpNotApp = do 
     i <- getPos
     o <- binaryOpName
     try
       (do t1 <- atom
           return (SBinaryOp i o (Just t1) Nothing))
       <|> return (SBinaryOp i o Nothing Nothing)

atom :: P SNTerm
atom = (flip SConst <$> const <*> getPos)
       <|> flip SV <$> var <*> getPos
       <|> unaryOp
       <|> binaryOp
      --  <|> unaryOpNotApp
       <|> parens stm

lam :: P SNTerm
lam = do i <- getPos
         reserved "fun"
         vs <- binders
         reservedOp "->"
         SLam i vs <$> stm

-- Nota el parser app también parsea un solo atom.
app :: P SNTerm
app = do i <- getPos
         f <- atom
         args <- many atom
         return (foldl (SApp i) f args)

ifz :: P SNTerm
ifz = do i <- getPos
         reserved "ifz"
         c <- stm
         reserved "then"
         t <- stm
         reserved "else"
         SIfZ i c t <$> stm

binding :: P [(Name, STy)]
binding = do vs <- many1 var
             reservedOp ":"
             ty <- typeP
             return (fmap (,ty) vs)

binders :: P [(Name, STy)]
binders = do vs <- many (parens binding)
             return (concat vs)
          <|> return []

fix :: P SNTerm
fix = do i <- getPos
         reserved "fix"
         [(f, fty)] <- parens binding
         [(x, xty)] <- parens binding
         reservedOp "->"
         SFix i f fty x xty <$> stm

letIn :: P SNTerm
letIn = do i <- getPos
           reserved "let"
           isRec <- (reserved "rec" >> return True ) <|> return False
           v <- var
           vs <- binders
           reservedOp ":"
           ty <- typeP
           reservedOp "="
           t <- stm
           reserved "in"
           t' <- stm
           (if isRec then
                return (SRec i v vs ty t t')
            else
                return (SLet i v vs ty t t')) 

-- | Parser de términos
stm :: P SNTerm
stm = app <|> lam <|> ifz <|> unaryOp <|> binaryOp <|> fix <|> letIn

-- | Parser de declaraciones
decl :: P (SDecl SNTerm)
decl = declTerm <|> declTy

declTerm :: P (SDecl SNTerm)
declTerm = do 
         i <- getPos
         reserved "let"
         isRec <- (reserved "rec" >> return True ) <|> return False
         v <- var
         vs <- binders
         reservedOp ":"
         ty <- typeP
         reservedOp "="
         t <- stm
         (if isRec then
              return (SDRec i v vs ty t)
          else
              return (SDLet i v vs ty t))

declTy :: P (SDecl a)
declTy = do i <- getPos
            reserved "type"
            v <- tyvar
            reservedOp "="
            SDType i v <$> typeP
       
-- | Parser de programas (listas de declaraciones)
program :: P [SDecl SNTerm]
program = many decl

-- | Parsea una declaración a un término
-- Útil para las sesiones interactivas
declOrSTm :: P (Either (SDecl SNTerm) SNTerm)
declOrSTm =  try (Right <$> stm) <|> (Left <$> decl)
-- Corre un parser, chequeando que se pueda consumir toda la entrada
runP :: P a -> String -> String -> Either ParseError a
runP p s filename = runParser (whiteSpace *> p <* eof) () filename s

--para debugging en uso interactivo (ghci)
parse :: String -> SNTerm
parse s = case runP stm s "" of
            Right t -> t
            Left _ -> error ("no parse: " ++ show s)

data Mode = Interactive
            | Typecheck
            | Bytecompile
            | Closurecompile
            | Run

-- | Parser de banderas
parseMode :: OptApp.Parser Mode
parseMode =
      OptApp.flag' Typecheck (OptApp.long "typecheck" <> OptApp.short 't' <> OptApp.help "Solo chequear tipos")
  OptApp.<|> OptApp.flag' Bytecompile (OptApp.long "bytecompile" <> OptApp.short 'c' <> OptApp.help "Compilar a la BVM")
  OptApp.<|> OptApp.flag' Closurecompile (OptApp.long "cc" <> OptApp.short 'C' <> OptApp.help "Compilar Funciones de Alto Orden")
  OptApp.<|> OptApp.flag' Run (OptApp.long "run" <> OptApp.short 'r' <> OptApp.help "Ejecutar bytecode en la BVM")
  OptApp.<|> OptApp.flag Interactive Interactive (OptApp.long "interactive" <> OptApp.short 'i' <> OptApp.help "Ejecutar en forma interactiva" )

-- | Parser de opciones general, consiste de un modo y una lista de archivos a procesar
parseArgs :: OptApp.Parser (Mode,[FilePath])
parseArgs = (,) <$> parseMode <*> OptApp.many (OptApp.argument OptApp.str (OptApp.metavar "FILES..."))