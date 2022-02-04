{-# LANGUAGE
    RebindableSyntax,
    DeriveFunctor,
    RankNTypes,
    GADTs,
    DataKinds,
    PolyKinds,
    TypeOperators
#-}

import Prelude hiding ((>>=))
import Data.Kind (Type)

data Rose a = V a | T [Rose a] deriving (Functor, Eq, Show)

type Shp = Rose ()

infixr 1 ~>
type (a ~> b) = forall x . a x -> b x

class IFunctor (h :: (a -> Type) -> a -> Type) where
    imap :: (f ~> g) -> (h f ~> h g)

data RComb :: ((Shp, Shp) -> Type) -> (Shp, Shp) -> Type where
    Seq :: k '(a, b) -> k '(b, c) -> RComb k '(a, c)
    Par :: k '(a, b) -> k '(c, d) -> RComb k '(T [a, c], T [b, d])
    Inv :: k '(a, b) -> RComb k '(b, a)

instance IFunctor RComb where
    imap f (Seq q r) = Seq (f q) (f r)
    imap f (Par q r) = Par (f q) (f r)
    imap f (Inv q) = Inv (f q)

class IFunctor m => IMonad m where
    skip :: f ~> m f
    extend :: (f ~> m g) -> (m f ~> m g)

(>>=) :: IMonad m => forall x . m f x -> (f ~> m g) -> m g x
(>>=) v k = extend k v

pure :: IMonad m => f ~> m f
pure = skip

data IFree :: ((a -> Type) -> a -> Type) -> (a -> Type) -> a -> Type where
    Ret :: c x -> IFree f c x
    Do :: f (IFree f c) x -> IFree f c x

instance IFunctor h => IFunctor (IFree h) where
    imap k (Ret x) = Ret (k x)
    imap k (Do op) = Do (imap (imap k) op)

instance IFunctor h => IMonad (IFree h) where
    skip x = Ret x
    extend k (Ret x) = k x
    extend k (Do op) = Do (imap (extend k) op)

tConst :: Type -> (Shp, Shp) -> Type
tConst t _ = t

type W = V '()

data Nat = Z | S Nat

data Test :: (Nat -> *) -> *

fun :: * -> Nat -> *
fun t _ = t

-- IFree RComb (tConst t) x = IFree RComb (tConst t) x

infixl 1 <:>
(<:>) :: IFree RComb (tConst t) '(a, b) -> IFree RComb (tConst t) '(b, c) -> IFree RComb (tConst t) '(a, c)
(<:>) q r = Do (Seq q r)

infixl 1 <|>
(<|>) :: IFree RComb (tConst t) '(a, b) -> IFree RComb (tConst t) '(c, d) -> IFree RComb (tConst t) '(T [a, c], T [b, d])
(<|>) q r = Do (Par q r)

inv :: IFree RComb (tConst t) '(a, b) -> IFree RComb (tConst t) '(b, a)
inv q = Do (Inv q)

--pi1 :: IFree RComb (tConst String) '(T [a, b], a)
--pi1 = Ret ("pi1" :: tConst String '(T [a, b], a))
