module Containers.Tuple2 

import public Rose
import public Data.Vect
import public Containers2
import Data.String

public export
Holes (Rose Unit) where
    holes (V _) = 1
    holes (T ts) = sum (map holes ts)

public export
Tuple : Type
Tuple = Rose Unit

public export
concatWith : Show a => String -> Vect n a -> String
concatWith _ [] = ""
concatWith _ [x] = show x
concatWith s (x :: xs) = show x ++ s ++ concatWith s xs

public export
Show Tuple where
    show (V _) = "."
    show (T xs) = "<" ++ concatWith ", " xs ++ ">"

public export
TData : Tuple -> Type -> Type
TData t a = Vect (holes t) a

public export
Typ : Type
Typ = (Tuple, Tuple)

public export
TyData : Typ -> Type -> Type
TyData (x, y) a = (TData x a, TData y a)

public export
W : Tuple
W = V ()

public export
data Block = Bloc Typ String

public export
Show Block where
    show (Bloc (d, c) n) = padRight 10 ' ' n ++ padRight 30 ' ' (show d) ++ show c
