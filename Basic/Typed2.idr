module Basic.Typed2

import Effects.Algebraic
import Data.List
import Data.String
import Data.Vect

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
build a b s = Var $ Bloc (genTuple a, genTuple b) s

interface IsType (x : a) (t : v) | x where
    dum : Unit
    dum = ()

{f : Type -> Type} ->
{a : Type} ->
{x : f (Free f a)} ->
{t : v} ->
IsType x t =>
IsType (Op {f = f} {a = a} x) t where
    dum = ()

{f : Type -> Type} ->
{a : Type} ->
{x : a} ->
{t : v} ->
IsType (Var {f = f} {a = (a, v)} (x, t)) t where
    dum = ()

argList : {k : Type} -> {t : Type} -> Vect (S n) k -> Vect (S n) t -> Type
argList xs ts = foldl1 (,) (zipWith IsType xs ts)

public export
data RComb : (k : Type) -> Type where
    Seq : (x, y : k) -> argList {t = Typ} [x, y] [(a, b), (b, c)] => RComb k

interface Funct (f : Type -> Type) where
    fmap : (a -> b) -> f a -> f b

--public export
--Functor RComb where
--    map f (Seq q r) = Seq (f q) (f r)

--data Arith : (k : Type) -> Type where
--    App : (x, y : k) -> argList [x, y] [Arrow a b, a] => Arith k

--{k : Type} -> {x : k} -> {y : k} -> {a : Typ} -> {b : Typ} ->
--argList [x, y] [Arrow a b, a] =>
--IsType (App x y) b


