module Scratch.Hardware2

import Effects.Algebraic
import Data.Vect

data Hard : (k : Type) -> Type where
    Map : (a -> b) -> k -> Hard k
    Fold : (a -> b -> b) -> k -> Hard k
    InProd : k -> k -> Hard k
    ElemProd : k -> k -> Hard k

Functor Hard where
    map f (Map g v ) = Map g (f v)
    map f (Fold g v) = Fold g (f v)
    map f (InProd v w) = InProd (f v) (f w)
    map f (ElemProd v w) = ElemProd (f v) (f w)

hmap : (a -> b) -> Free Hard c -> Free Hard c
hmap f v = Op (Map f v)

hfold : (a -> b -> b) -> Free Hard c -> Free Hard c
hfold f v = Op (Fold f v)

hinProd : Free Hard a -> Free Hard a -> Free Hard a
hinProd v w = Op (InProd v w)

helemProd : Free Hard a -> Free Hard a -> Free Hard a
helemProd v w = Op (ElemProd v w)

genVec : Vect n a -> Free Hard (Vect n a)
genVec = Var

test : Free Hard (Vect 3 Int)
test = hinProd (hmap (+3) (genVec [1,2,3])) (genVec [4,6,4]) 

