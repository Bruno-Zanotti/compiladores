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
import Data.Char ( isNumber, ord )
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
         reservedNames = ["let", "in", "rec", "fun", "fix", "then", "else", "succ", "pred", "ifz", "Nat", "type"],
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
typeP = try (do 
          x <- tyatom
          reservedOp "->"
          y <- typeP
          return (SFunTy x y))
      <|> tyatom 
          
const :: P Const
const = CNat <$> num

unaryOpName :: P UnaryOp
unaryOpName =
      (reserved "succ" >> return Succ)
  <|> (reserved "pred" >> return Pred)

unaryOp :: P SNTerm
unaryOp = try (unaryOpApp <|> unaryOpNotApp)

unaryOpApp :: P SNTerm
unaryOpApp = do
  i <- getPos
  o <- unaryOpName
  a <- atom
  return (SUnaryOp i o (Just a))

unaryOpNotApp :: P SNTerm
unaryOpNotApp = do
  i <- getPos
  o <- unaryOpName
  return (SUnaryOp i o Nothing)

atom :: P SNTerm
atom = (flip SConst <$> const <*> getPos)
       <|> flip SV <$> var <*> getPos
       <|> unaryOpNotApp
       <|> parens stm

lam :: P SNTerm
lam = do i <- getPos
         reserved "fun"
         vs <- binders
         reservedOp "->"
         t <- stm
         return (SLam i vs t)

-- Nota el parser app también parsea un solo atom.
app :: P SNTerm
app = (do i <- getPos
          f <- atom
          args <- many atom
          return (foldl (SApp i) f args))

ifz :: P SNTerm
ifz = do i <- getPos
         reserved "ifz"
         c <- stm
         reserved "then"
         t <- stm
         reserved "else"
         e <- stm
         return (SIfZ i c t e)

-- binding :: P (Name, STy)
-- binding = do v <- var
--              reservedOp ":"
--              ty <- typeP
--              return (v, ty)

binding :: P [(Name, STy)]
binding = do vs <- many1 var
             reservedOp ":"
             ty <- typeP
             return (fmap (\v -> (v,ty)) vs)

binders :: P [(Name, STy)]
-- binders = concat (many (parens binding)) <|> return []
binders = do vs <- many (parens binding)
             return (concat vs)
          <|> return []

fix :: P SNTerm
fix = do i <- getPos
         reserved "fix"
         [(f, fty)] <- parens binding
         [(x, xty)] <- parens binding
         reservedOp "->"
         t <- stm
         return (SFix i f fty x xty t)

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
           case isRec of
             True -> return (SRec i v vs ty t t')
             _    -> return (SLet i v vs ty t t') 

-- | Parser de términos
stm :: P SNTerm
stm = app <|> lam <|> ifz <|> unaryOp <|> fix <|> letIn

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
         case isRec of
           True -> return (SDRec i v vs ty t)
           _    -> return (SDLet i v vs ty t)

declTy :: P (SDecl a)
declTy = do
       i <- getPos
       reserved "type"
       v <- tyvar
       reservedOp "="
       ty <- typeP
       return (SDType i v ty)
       
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
            Left e -> error ("no parse: " ++ show s)

data Mode = Interactive
            | Typecheck
            | Bytecompile
            | Run

-- | Parser de banderas
parseMode :: OptApp.Parser Mode
parseMode =
      OptApp.flag' Typecheck (OptApp.long "typecheck" <> OptApp.short 't' <> OptApp.help "Solo chequear tipos")
  OptApp.<|> OptApp.flag' Bytecompile (OptApp.long "bytecompile" <> OptApp.short 'c' <> OptApp.help "Compilar a la BVM")
  OptApp.<|> OptApp.flag' Run (OptApp.long "run" <> OptApp.short 'r' <> OptApp.help "Ejecutar bytecode en la BVM")
  OptApp.<|> OptApp.flag Interactive Interactive (OptApp.long "interactive" <> OptApp.short 'i' <> OptApp.help "Ejecutar en forma interactiva" )

-- | Parser de opciones general, consiste de un modo y una lista de archivos a procesar
parseArgs :: OptApp.Parser (Mode,[FilePath])
parseArgs = (,) <$> parseMode <*> OptApp.many (OptApp.argument OptApp.str (OptApp.metavar "FILES..."))