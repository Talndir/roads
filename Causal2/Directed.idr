module Causal2.Directed

import public Causal2.Data

public export
data DComb : (k : DShp' -> Type) -> DShp' -> Type where
    Seq : k (a, b) -> k (b, c) -> DComb k (a, c)
    Par : k (a, b) -> k (c, d) -> DComb k ([a, c], [b, d])
    Inv : {a', b' : DShp} -> Opp a a' => Opp b b' => k (a, b) -> DComb k (b', a')
    Del : {a : DShp} -> Rights a => Data Right a -> DComb k (a, a)

public export
IFunctor DComb where
    imap f (Seq q r) = Seq (f q) (f r)
    imap f (Par q r) = Par (f q) (f r)
    imap f (Inv q) = Inv (f q)
    imap f (Del d) = Del d

public export
data Interp : DShp' -> Type where
    Inter : {x, y : DShp}
         -> ((Data Right x, Data Left y) -> (Data Left x, Data Right y))
         -> Interp (x, y)

public export
record DBlock (d : DShp') where
    constructor MkDBlock
    name : String
    func : Interp d

public export
DRuby : DShp' -> Type
DRuby = IFree DComb DBlock

infixl 3 <:>
public export
(<:>) : DRuby (a, b) -> DRuby (b, c) -> DRuby (a, c)
(q <:> r) = Do (Seq q r)

infixl 3 <|>
public export
(<|>) : DRuby (a, b) -> DRuby (c, d) -> DRuby ([a, c], [b, d])
(q <|> r) = Do (Par q r)

public export
inv : {a', b' : DShp} -> Opp a a' => Opp b b' => DRuby (a, b) -> DRuby (b', a')
inv q = Do (Inv q)

public export
del : {a : DShp} -> Rights a => Data Right a -> DRuby (a, a)
del d = Do (Del d)
