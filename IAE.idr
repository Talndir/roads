module IAE

import public Indexed

public export
data IFree : (f : (a -> Type) -> a -> Type) -> (c : a -> Type) -> a -> Type where
    Ret : forall x . c x -> IFree f c x
    Do : f (IFree f c) x -> IFree f c x

public export
{a : Type} -> {h : (a -> Type) -> a -> Type} -> IFunctor h => IFunctor (IFree h) where
    imap k (Ret x) = Ret (k x)
    imap {f} {g} k (Do op) = Do (imap {f=IFree h f} {g=IFree h g} (imap {f} {g} k) op)

public export
{a : Type} -> {h : (a -> Type) -> a -> Type} -> IFunctor h => IMonad a (IFree h) where
    skip x = Ret x
    extend k (Ret x) = k x
    extend k (Do op) = Do (imap {f=IFree h f} {g=IFree h g} (extend {m=IFree h} k) op)

public export
fold :  {f : (a -> Type) -> (a -> Type)} -> IFunctor f =>
        {c : a -> Type} -> {d : a -> Type} -> (forall x . c x -> d x) ->
        (forall x . f d x -> d x) ->
        (forall x . IFree f c x -> d x)
fold gen _ (Ret x) = gen x
fold gen alg (Do op) = alg (imap {f=IFree f c} {g=d} (fold gen alg) op)

public export
Gen : {a, b : Type} -> {f : (a -> Type) -> a -> Type} -> IFunctor f => {t : a} -> b -> IFree f (Const a b) t
Gen {t} x = Ret (x, (t ** Refl))
