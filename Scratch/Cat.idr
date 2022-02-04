module Scratch.Cat

infixr 9 <.>
interface Category (k : Type -> Type -> Type) where
    id : a `k` a
    (<.>) : (b `k` c) -> (a `k` b) -> (a `k` c)

infixr 3 <^>
interface Category k => Cartesian k where
    (<^>) : (a `k` b) -> (a `k` c) -> (a `k` (b, c))
    exl : (a, b) `k` a
    exr : (a, b) `k` b

infixr 3 ->>
data (->>) : Type -> Type -> Type where
    Exp : a -> b -> a ->> b

interface Cartesian k => Closed k where
    apply : (a ->> b, a) `k` b
    curry : ((a, b) `k` c) -> (a `k` (b ->> c))
    uncurry : (a `k` (b ->> c)) -> ((a, b) `k` c)

interface Category k => Terminal k where
    final : a `k` ()
