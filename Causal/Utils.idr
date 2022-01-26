module Causal.Utils

import Causal.Defs

public export
underT : {xs : Vect n (Rose a)} -> {ys : Vect m (Rose b)} -> (pf : T xs = T ys) -> xs = ys
underT Refl = Refl

public export
underT' : {x : Rose a} -> {y : Rose a} -> (pf : T (x :: xs) = T (y :: ys)) -> (x = y, T xs = T ys)
underT' Refl = (Refl, Refl)

public export
addEq : {x, y : a} -> {xs, ys : Vect n a} -> x = y -> xs = ys -> (x :: xs) = (y :: ys)
addEq Refl Refl = Refl

public export
addToVect : {xs : Vect n (Rose a)} -> {ys : Vect m (Rose b)}
         -> {x : Rose a} -> {y : Rose b}
         -> Equal {a = Rose a} {b = Rose b} x y
         -> Equal {a = Rose a} {b = Rose b} (T xs) (T ys)
         -> Equal {a = Rose a} {b = Rose b} (T (x :: xs)) (T (y :: ys))
addToVect Refl Refl = Refl

public export
splitPf : (a, b) = (x, y) -> (a = x, b = y)
splitPf Refl = (Refl, Refl)
