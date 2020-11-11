{-|
Module      : Common
Description : Algunas operaciones generales
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Common where

--------------------------
-- Posición en un archivo
--------------------------
type Line = Int
type Column = Int

data Pos = NoPos             -- ^ No hay info de posición
         | Pos !Line !Column -- ^ Posición en un archivo.

instance Semigroup Pos where
  i <> NoPos = i
  _ <> i     = i

instance Monoid Pos where
  mempty = NoPos

instance Show Pos where
   show (Pos line column) = "("++show line++","++show column++")"
   show NoPos = ""

---------------------
-- Utility functions
--------------------
abort :: String -> a
abort s = error ("INTERNAL ERROR: " ++ s)

infixl 1 |>
(|>) :: a -> (a -> b) -> b
x |> f = f x

-- wordsWhen     :: (Char -> Bool) -> String -> [String]
-- wordsWhen p s =  case dropWhile p s of
--                       "" -> []
--                       s' -> w : wordsWhen p s''
--                             where (w, s'') = break p s'

dropExtension :: String -> String
dropExtension (x:xs) = case x of
                        '.' -> []
                        _   -> x: (dropExtension xs)