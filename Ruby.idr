module Ruby

import AE
import public Tuple

public export
data RTuple : (k : Type) -> Type where
    Apl : k -> RTuple k
    Apr : k -> RTuple k
    App : k -> k -> RTuple k
    Rev : k -> RTuple k
    Pair : k -> k -> RTuple k

public export
Functor RTuple where
    map f (Apl v) = Apl (f v)
    map f (Apr v) = Apr (f v)
    map f (App v w) = App (f v) (f w)
    map f (Rev v) = Rev (f v)
    map f (Pair v w) = Pair (f v) (f w)

public export
data RComb : (k : Type) -> Type where
    Seq : k -> k -> RComb k
    SeqL : k -> k -> RComb k
    SeqR : k -> k -> RComb k
    Par : k -> k -> RComb k
    Inv : k -> RComb k
    Bes : k -> k -> RComb k
    Bel : k -> k -> RComb k
    Loop : k -> RComb k

public export
Functor RComb where
    map f (Seq q r) = Seq (f q) (f r)
    map f (SeqL q r) = SeqL (f q) (f r)
    map f (SeqR q r) = SeqR (f q) (f r)
    map f (Par q r) = Par (f q) (f r)
    map f (Inv q) = Inv (f q)
    map f (Bes q r) = Bes (f q) (f r)
    map f (Bel q r) = Bel (f q) (f r)
    map f (Loop q) = Loop (f q)

public export
build : Nat -> Nat -> String -> Free f Block
build a b s = Var $ Bloc (genTuple a, genTuple b) s
