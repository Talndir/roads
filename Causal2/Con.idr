module Causal2.Con

import Data.HVect

import Causal2.Data
import Causal2.Dec

infixl 1 -=
prefix 1 <<
prefix 1 >>
infixl 1 ~~

public export
data Con : Type -> Type where
    (-=) : a -> a -> Con a
    (<<) : a -> Con a
    (>>) : a -> Con a
    (~~) : a -> a -> Con a
    Fk : a -> a -> a -> Con a

public export
ConMap : Con DShp -> Type
ConMap (x -= y) = x = y
ConMap (<< x) = Lefts x
ConMap (>> x) = Rights x
ConMap (x ~~ y) = Opp x y
ConMap (Fk x y z) = Fork x y z

public export
data HCon : Vect n (Con DShp) -> Type where
    HEmpty : HCon []
    HCons : ConMap x -> HCon xs -> HCon (x :: xs)

public export
Nil : HCon []
Nil = HEmpty

public export
(::) : ConMap x -> HCon xs -> HCon (x :: xs)
r :: rs = HCons r rs

public export
try1 : (r : Con DShp) -> Maybe (ConMap r)
try1 (x -= y) with (decEq x y)
    _ | Yes p = Just p
    _ | No p = Nothing
try1 (<< x) with (decLeft x)
    _ | Yes p = Just p
    _ | No p = Nothing
try1 (>> x) with (decRight x)
    _ | Yes p = Just p
    _ | No p = Nothing
try1 (x ~~ y) with (decOpp x y)
    _ | Yes p = Just p
    _ | No p = Nothing
try1 (Fk x y z) with (decFork x y z)
    _ | Yes p = Just p
    _ | No p = Nothing

public export
make : Vect n (Con DShp) -> Type -> Type
make [] t = t
make (r :: rs) t = ConMap r => make rs t

public export
try : (rs : Vect n (Con DShp)) -> make rs a -> Maybe a
try [] f = Just f
try (r :: rs) f = do
    p <- try1 r
    try rs (f @{p})
