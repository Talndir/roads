module Tuple

import public Rose
import Data.String

public export
Tuple : Type
Tuple = Rose Nat

public export
concatWith : Show a => String -> List a -> String
concatWith _ [] = ""
concatWith _ [x] = show x
concatWith s (x :: xs) = show x ++ s ++ concatWith s xs

public export
Show Tuple where
    show (V x) = "." ++ show x
    show (T xs) = "<" ++ concatWith ", " (toList xs) ++ ">"

public export
Typ : Type
Typ = (Tuple, Tuple)

public export
W : Tuple
W = V 0

public export
data Block = Bloc Typ String

public export
Show Block where
    show (Bloc (d, c) n) = padRight 10 ' ' n ++ padRight 30 ' ' (show d) ++ show c
