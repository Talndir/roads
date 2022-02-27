module Causal2.Typed

import public Causal2.Data
import public Causal2.Directed
import public Causal2.Con

public export
data TComb : (k : TShp' -> Type) -> TShp' -> Type where
    Seq : k (a, b) -> k (b, c) -> TComb k (a, c)
    Par : k (a, b) -> k (c, d) -> TComb k ([a, c], [b, d])
    Inv : k (a, b) -> TComb k (b, a)
    Del : TComb k (a, a)

public export
IFunctor TComb where
    imap f (Seq q r) = Seq (f q) (f r)
    imap f (Par q r) = Par (f q) (f r)
    imap f (Inv q) = Inv (f q)
    imap f Del = Del

public export
record TBlock (t : TShp') where
    constructor MkTBlock
    name : String
    type : TShp'
    nv : Nat
    nc : Nat
    con : forall a . Vect nv a -> Vect nc (Con a)
    vars : forall a . (Rose a, Rose a) -> Vect nv (Rose a)
    res : Vect nv DShp -> DShp'
    resNat : Vect nv NShp -> NShp'
    run : (vs : Vect nv DShp) -> make (con vs) (DBlock (res vs))

public export
TRuby : TShp' -> Type
TRuby = IFree TComb TBlock

infixl 3 <:>
public export
(<:>) : TRuby (a, b) -> TRuby (b, c) -> TRuby (a, c)
(q <:> r) = Do (Seq q r)

infixl 3 <|>
public export
(<|>) : TRuby (a, b) -> TRuby (c, d) -> TRuby ([a, c], [b, d])
(q <|> r) = Do (Par q r)

public export
inv : TRuby (a, b) -> TRuby (b, a)
inv q = Do (Inv q)

public export
del : TRuby (a, a)
del = Do Del
