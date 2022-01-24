module Containers.Containers

import Data.Fin
import Data.Vect

infix 3 |>
data Cont : (s : Type) -> (p : s -> Type) -> Type where
    (|>) : (s : Type) -> (p : s -> Type) -> Cont s p

infix 3 #!
data Ext : Cont s p -> Type -> Type where
    (#!) : (s' : s) -> (f : p s' -> a) -> Ext (s |> p) a

Functor (Ext (s |> p)) where
    map g (n #! f) = n #! (g . f)

Lst : Type -> Type
Lst a = Ext (Nat |> Fin) a

gen : (n : Nat) -> Vect n (Fin n)
gen Z = []
gen (S m) = FZ :: map FS (gen m)

Show a => Show (Lst a) where
    show (n #! f) = show (map f (gen n))

tst : Lst Nat
tst = 3 #! finToNat
