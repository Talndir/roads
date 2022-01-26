module Causal.Defs

import public Data.Vect
import public Data.HVect
import public Indexed

-- Rose trees

public export
data Rose a = V a | T (Vect n (Rose a))

public export
Show a => Show (Rose a) where
    show (V x) = show x
    show (T rs) = show rs

public export
Functor Rose where
    map f (V x) = V (f x)
    map f (T rs) = T (map (map f) rs)

public export
Shp : Type
Shp = Rose Unit

public export
Shp' : Type
Shp' = (Shp, Shp)

public export
W : Rose Unit
W = V ()


-- Directions

public export
data Dir = In | Out

public export
Eq Dir where
    In == In = True
    Out == Out = True
    _ == _ = False

public export
swap : Dir -> Dir
swap In = Out
swap Out = In

public export
I, O : Rose Dir
I = V In
O = V Out

public export
DShp : Type
DShp = Rose Dir

public export
DShp' : Type
DShp' = (DShp, DShp)

public export
mk : Dir -> Rose a -> DShp
mk d = map (const d)


-- Shapes

public export
nil : Functor f => f a -> f Unit
nil = map (const ())

public export
Shape : {f : Type -> Type} -> Functor f => f Unit -> Type -> Type
Shape x a = (y : f a ** nil y = x)

public export
(Functor f, Show a, Show (f a)) => Show (Shape {f=f} s a) where
    show (y ** p) = show y

public export
Tuple : Shp -> Type -> Type
Tuple = Shape {f=Rose}

public export
Typ : Shp' -> Type -> Type
Typ (ts, us) a = (Tuple ts a, Tuple us a)


-- Properties

public export
data Is : Dir -> Rose Dir -> Type where
    TIs : {xs : Vect n (Rose Dir)} -> HVect (map (Is d) xs) -> Is d (T xs)
    VIs : Is d (V d)

public export
data Same : Eq a => Rose a -> Rose a -> Type where
    TSame : Eq a => {xs, ys : Vect n (Rose a)} -> HVect (zipWith Same xs ys) -> Same (T xs) (T ys)
    VSame : Eq a => {x : a} -> Same (V x) (V x)

public export
data Compl : DShp -> DShp -> Type where
    TCompl : {xs, ys : Vect n DShp} -> HVect (zipWith Compl xs ys) -> Compl (T xs) (T ys)
    VCompl1 : Compl (V In) (V Out)
    VCompl2 : Compl (V Out) (V In)


-- Ruby

public export
compl : DShp -> DShp
compl = map swap

public export
data RComb : (k : DShp' -> Type) -> DShp' -> Type where
    Seq : k (a, b) -> k (compl b, c) -> RComb k (a, c)
    Par : k (a, b) -> k (c, d) -> RComb k (T [a, c], T [b, d])
    Inv : k (a, b) -> RComb k (b, a)

public export
IFunctor RComb where
    imap f (Seq q r) = Seq (f q) (f r)
    imap f (Par q r) = Par (f q) (f r)
    imap f (Inv q) = Inv (f q)
