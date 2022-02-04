module Scratch.Minimal

import Data.Vect
import Data.HVect

data Rose a = V a | T (Vect n (Rose a))

Functor Rose where
    map f (V x) = V (f x)
    map f (T rs) = T (map (map f) rs)

Shp : Type
Shp = Rose Unit

data Dir = In | Out

DShp : Type
DShp = Rose Dir
DShp' : Type
DShp' = (DShp, DShp)

I, O : DShp
I = V In
O = V Out

nil : Functor f => f a -> f Unit

Shape : {f : Type -> Type} -> Functor f => f Unit -> Type -> Type

Tuple : Shp -> Type -> Type

-- A witness for the equation `map (const d) x = x`
data Is : Dir -> Rose Dir -> Type where
    TIs : {xs : Vect n (Rose Dir)} -> HVect (map (Is d) xs) -> Is d (T xs)
    VIs : Is d (V d)

-- A witness for the equation `map swap x = y` (where swap swaps In and Out)
data Compl : (x : DShp) -> (y : DShp) -> Type where
    [search x, search y]
    TCompl : {xs, ys : Vect n DShp} -> HVect (zipWith Compl xs ys) -> Compl (T xs) (T ys)
    VCompl1 : Compl (V In) (V Out)
    VCompl2 : Compl (V Out) (V In)

data RComb : (k : DShp' -> Type) -> DShp' -> Type where
    Seq : {auto pf : Compl b b'} -> k (a, b) -> k (b', c) -> RComb k (a, c)     -- Infix `<:>`
    Par : k (a, b) -> k (c, d) -> RComb k (T [a, c], T [b, d])                  -- Infix `<|>`
    Inv : k (a, b) -> RComb k (b, a)                                            -- Prefix `inv`

data IFree : (f : (a -> Type) -> a -> Type) -> (c : a -> Type) -> a -> Type where

data Interp : (a : Type) -> (ds : DShp') -> Type where

Ruby : Type -> DShp' -> Type
Ruby a x = IFree RComb (Interp a) x

infixl 3 <:>
(<:>) : {auto pf : Compl b b'} -> Ruby t (a, b) -> Ruby t (b', c) -> Ruby t (a, c)

infixl 3 <|>
(<|>) : Ruby t (a, b) -> Ruby t (c, d) -> Ruby t (T [a, c], T [b, d])

inv : Ruby t (a, b) -> Ruby t (b, a)

fork2 : {x, y : DShp}
     -> {auto pin : Is In x} -> {auto pout : Is Out y} -> {auto pcompl : Compl x y}
     -> Ruby a (y, T [y, x])

rsh : {x,y,z,p,q,r : DShp}
    -> {auto xp : Compl x p} -> {auto yq : Compl y q} -> {auto zr : Compl z r}
    -> Ruby a (T [x, T [y, z]], T [T [p, q], r])

outl : {x, y, z: DShp}
    -> {auto pfin : Is In y} -> {auto pfc : Compl x z}
    -> Ruby a (T [x, y], z)

-- This fails unless I provide type annotations for each subterm
fails : Ruby a (T [O, I], T [T [O, O], I])
fails = inv outl <:> (inv fork2 <|> fork2) <:> rsh

-- But if I split it, it passes
p1 : Ruby a (T [O, I], T [T [I, O], I])
p1 = inv outl

p2 : Ruby a (T [T [O, I], O], T [T [O, O], I])
p2 = (inv fork2 <|> fork2) <:> rsh

works : Ruby a (T [O, I], T [T [O, O], I])
works = p1 <:> p2

