module Basic.Ruby

import Effects.Algebraic
import public Tuple

public export
data RComb : (k : Type) -> Type where
    Seq : k -> k -> RComb k
    Par : k -> k -> RComb k
    Inv : k -> RComb k
    Bes : k -> k -> RComb k
    Bel : k -> k -> RComb k
    Loop : k -> RComb k

public export
Functor RComb where
    map f (Seq q r) = Seq (f q) (f r)
    map f (Par q r) = Par (f q) (f r)
    map f (Inv q) = Inv (f q)
    map f (Bes q r) = Bes (f q) (f r)
    map f (Bel q r) = Bel (f q) (f r)
    map f (Loop q) = Loop (f q)

public export
build : Nat -> Nat -> String -> Free f Block
build a b s = Var $ Bloc (genTuple a, genTuple b) s

public export
Ruby : Type
Ruby = Free RComb Block
