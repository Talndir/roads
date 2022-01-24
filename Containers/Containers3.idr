module Containers.Containers3

import public Data.List
import public Data.Vect
import public Data.Fin
import public Data.Nat
import public Rose

public export
Cont : (s : Type -> Type) -> (a : Type) -> Type
Cont s a = (n : Nat ** (s (Fin n), Vect n a))

public export
interface Functor s => Container s where
    unmake : s a -> Cont s a
    make : Cont s a -> s a
    make (n ** (p, v)) = map (flip index v) p

public export
(Show a, Functor s, Show (s Nat)) => Show (Cont s a) where
    show (n ** (p, v)) = show (map finToNat p) ++ " ::: " ++ show v

public export
Container Rose where
    unmake (V x) = (1 ** (V FZ, [x]))
    unmake (T rs) = foldr f (0 ** (T [], [])) rs where
        join : {n, ns : Nat} -> Rose (Fin n) -> Rose (Fin ns) -> Rose (Fin (n + ns))
        join p (T ps) = T (map (weakenN ns) p :: map (map (shift n)) ps)
        join p (V _) = T [map (weakenN ns) p]
        f : Rose a -> Cont Rose a -> Cont Rose a
        f x (ns ** (ps, vs)) = let (n ** (p, v)) = unmake x in (n + ns ** (join p ps, v ++ vs))
