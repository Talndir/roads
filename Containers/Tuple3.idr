module Containers.Tuple3

import public Containers3
import Data.String

public export
Tuple : Type -> Type
Tuple = Rose

public export
concatWith : Show a => String -> Vect n a -> String
concatWith _ [] = ""
concatWith _ [x] = show x
concatWith s (x :: xs) = show x ++ s ++ concatWith s xs

public export
Show a => Show (Tuple a) where
    show (V x) = "." ++ show x
    show (T xs) = "<" ++ concatWith ", " xs ++ ">"

public export
Typ : Type -> Type
Typ a = (Tuple a, Tuple a)

public export
W : Tuple Nat
W = V 0

public export
data Block a = Bloc (Typ a) String

public export
Show a => Show (Block a) where
    show (Bloc (d, c) n) = padRight 10 ' ' n ++ padRight 30 ' ' (show d) ++ show c
