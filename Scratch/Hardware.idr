module Scratch.Hardware

import AE
import Data.Vect

data Hard : (k : Type) -> Type where
    Map : (a -> b) -> Vect n a -> (Vect n b -> k) -> Hard k
    Fold : (a -> b -> b) -> Vect n a -> (b -> k) -> Hard k
    InProd : Vect n a -> Vect n a -> (a -> k) -> Hard k
    ElemProd : Vect n a -> Vect n a -> (Vect n a -> k) -> Hard k

Functor Hard where
    map f (Map g v h) = Map g v (f . h)
    map f (Fold g v h) = Fold g v (f . h)
    map f (InProd v w h) = InProd v w (f . h)
    map f (ElemProd v w h) = ElemProd v w (f . h)

hmap : (a -> b) -> Vect n a -> Free Hard (Vect n b)
hmap f v = Op (Map f v pure)

hfold : (a -> b -> b) -> Vect n a -> Free Hard b
hfold f v = Op (Fold f v pure)

hinProd : Num a => Vect n a -> Vect n a -> Free Hard a
hinProd v w = Op (InProd v w pure)

helemProd : Num a => Vect n a -> Vect n a -> Free Hard (Vect n a)
helemProd v w = Op (ElemProd v w pure)

genVec : Vect n a -> Free Hard (Vect n a)
genVec = Var

test : Free Hard Int
test = do
    v <- genVec [1, 2, 3]
    w <- hmap (+3) v
    u <- genVec [4, 6, 4]
    hinProd w u


