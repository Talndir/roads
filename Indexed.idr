module Indexed

public export
interface IFunctor (h : (a -> Type) -> a -> Type) where
    imap : {f : a -> Type} -> {g : a -> Type} -> (forall x . f x -> g x) -> (forall x . h f x -> h g x)

public export
interface IFunctor m => IMonad (a : Type) (m : (a -> Type) -> a -> Type) where
    skip : {f : a -> Type} -> {x : a} -> f x -> m f x
    extend : {f : a -> Type} -> {g : a -> Type} -> (forall x . f x -> m g x) -> (forall x . m f x -> m g x)

(>>=) : {a : Type} -> {m : (a -> Type) -> a -> Type} -> IMonad a m => {f : a -> Type} -> {g : a -> Type} -> (forall x . m f x -> (forall y . f y -> m g y) -> m g x)
(v >>= k) = extend {f} k v

pure : {a : Type} -> {m : (a -> Type) -> a -> Type} -> IMonad a m => {f : a -> Type} -> {x : a} -> f x -> m f x
pure = skip {f}

public export
Index : (f : Type -> Type) -> ((Unit -> Type) -> Unit -> Type)
Index f c _ = f (c ())

public export
{f : Type -> Type} -> Functor f => IFunctor (Index f) where
    imap k x = map k x

public export
{m : Type -> Type} -> Monad m => IFunctor (Index m) where
    imap k x = map k x

unitSingle : (f : Unit -> Type) -> (x : Unit) -> (f () = f x)
unitSingle f () = Refl
convertUnit : (f : Unit -> Type) -> (x : Unit) -> f x -> f ()
convertUnit f x v = rewrite unitSingle f x in v
convertUnit' : (f : Unit -> Type) -> (x : Unit) -> f () -> f x
convertUnit' f x v = rewrite sym (unitSingle f x) in v

public export
Const : (a : Type) -> Type -> (a -> Type)
Const a b x = (b, (y : a ** y = x))
