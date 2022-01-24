module Containers.Containers2

import Data.Fin
import public Data.Vect

public export
interface Holes s where
    holes : s -> Nat
    cmap : (a -> b) -> (n : s ** Vect (holes n) a) -> (n ** Vect (holes n) b)
    cmap f (x ** xs) = (x ** map f xs)

public export
Cont : (s : Type) -> Holes s => Type -> Type
Cont s a = (n : s ** Vect (holes n) a)

public export
(Show s, Holes s, Show a) => Show (Cont s a) where
    show (n ** v) = show n ++ " ::: " ++ show v

Holes Nat where
    holes = id

Lst : Type -> Type
Lst = Cont Nat

tst : Lst Nat
tst = (3 ** [0, 1, 2])

data BTreeS = Leaf | Branch BTreeS BTreeS

Holes BTreeS where
    holes Leaf = 1
    holes (Branch l r) = holes l + holes r

BTree : Type -> Type
BTree = Cont BTreeS

tst2 : BTree String
tst2 = (Branch (Branch Leaf Leaf) Leaf ** ["hello", "world", "!"])
