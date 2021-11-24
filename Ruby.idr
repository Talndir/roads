module Ruby

import AE
import Data.List
import Data.String

public export
data RTuple : (k : Type) -> Type where
    Apl : k -> RTuple k
    Apr : k -> RTuple k
    App : k -> k -> RTuple k
    Rev : k -> RTuple k
    Pair : k -> k -> RTuple k

public export
Functor RTuple where
    map f (Apl v) = Apl (f v)
    map f (Apr v) = Apr (f v)
    map f (App v w) = App (f v) (f w)
    map f (Rev v) = Rev (f v)
    map f (Pair v w) = Pair (f v) (f w)

public export
data RComb : (k : Type) -> Type where
    Seq : k -> k -> RComb k
    SeqL : k -> k -> RComb k
    SeqR : k -> k -> RComb k
    Par : k -> k -> RComb k
    Inv : k -> RComb k
    Bes : k -> k -> RComb k
    Bel : k -> k -> RComb k
    Loop : k -> RComb k

public export
Functor RComb where
    map f (Seq q r) = Seq (f q) (f r)
    map f (SeqL q r) = SeqL (f q) (f r)
    map f (SeqR q r) = SeqR (f q) (f r)
    map f (Par q r) = Par (f q) (f r)
    map f (Inv q) = Inv (f q)
    map f (Bes q r) = Bes (f q) (f r)
    map f (Bel q r) = Bel (f q) (f r)
    map f (Loop q) = Loop (f q)

public export
data Tuple : Type where
    W : Nat -> Tuple
    T : List Tuple -> Tuple

public export
concatWith : Show a => String -> List a -> String
concatWith _ [] = ""
concatWith _ [x] = show x
concatWith s (x :: xs) = show x ++ s ++ concatWith s xs

public export
Show Tuple where
    show (W 0) = "V"
    show (W x) = "." ++ show x
    show (T xs) = "<" ++ concatWith ", " xs ++ ">"

public export
Typ : Type
Typ = (Tuple, Tuple)

public export
data Block = Bloc Typ String

public export
Show Block where
    show (Bloc (d, c) n) = padRight 10 ' ' n ++ padRight 30 ' ' (show d) ++ show c

public export
V : Tuple
V = W 0

public export
genTuple : Nat -> Tuple
genTuple 1 = V
genTuple n = T (replicate n V)

public export
build : Nat -> Nat -> String -> Free f Block
build a b s = Var $ Bloc (genTuple a, genTuple b) s where

