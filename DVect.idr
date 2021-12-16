module DVect

import public Data.Vect

public export
data DVect : {a, b : Type} -> (f : a -> b -> Type) -> Vect n a -> Type where
    Nil : DVect f []
    (::) : (y : b ** f x y) -> DVect f xs -> DVect f (x :: xs)

public export
extract : {xs : Vect n a} -> DVect {a} {b} f xs -> Vect n b
extract (y :: ys) = fst y :: extract ys
extract [] = []
