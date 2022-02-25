module Scratch.Safe

import Effects.Algebraic
import Lambda
import Effects.Annotate
import Data.Vect

data Unify : TType -> TType -> Type where
    Unify_1 : Unify (TFree x) (TFree x)


data Typed : Type -> TType -> Type where
    Top : k -> Typed k t

TLam : TType -> Type -> Type
TLam t a = Typed (Free Lambda a) t

lapp : TLam (TFunc p q) a -> TLam p a -> TLam q a
lapp (Top f) (Top x) = Top (Op (LApp f x))

tryme : TLam (TFree "a") String
tryme = lapp f x where
    f : TLam (TFunc (TFree "a") (TFree "a")) String
    f = Top (Op (LLam "a" (Var "a")))
    x : TLam (TFree "a") String
    x = Top (Var "x")


data Lang : (k : Type) -> Type where
    Map : (a -> b) -> k -> Lang k
    Fold : (a -> b -> b) -> k -> Lang k
    InnerProd : k -> k -> Lang k

data Types : Type where
    TyVec : Nat -> Types -> Types
    TyVal : Type -> Types
    TyFunc : Types -> Types -> Types

data Typd : Type -> Types -> Type where
    Tp : k -> Typd k t

TLang : Types -> Type -> Type
TLang t a = Typd (Free Lang a) t

lmap : (a -> b) -> TLang (TyVec n (TyVal a)) c -> TLang (TyVec n (TyVal b)) c
lmap f (Tp v) = Tp (Op (Map f v))

lfold : (a -> b -> b) -> TLang (TyVec n (TyVal a)) c -> TLang (TyVal b) c
lfold f (Tp v) = Tp (Op (Fold f v))

linnerprod : Num a => TLang (TyVec n (TyVal a)) c -> TLang (TyVec n (TyVal a)) c -> TLang (TyVal a) c
linnerprod (Tp v) (Tp w) = Tp (Op (InnerProd v w))

lvec : (n : Nat) -> a -> TLang (TyVec n (TyVal a)) (Vect n a)
lvec n x = Tp . Var $ replicate n x

tst : TLang (TyVal Int) (Vect 8 Int)
tst = linnerprod v w where
    v : TLang (TyVec 8 (TyVal Int)) (Vect 8 Int)
    v = lmap (+4) (lvec 8 5)
    w : TLang (TyVec 8 (TyVal Int)) (Vect 8 Int)
    w = lvec 8 9

data Lang2 : (k : Type) -> Type where
    Map2 : (a -> b) -> Vect n a -> (Vect n b -> k) -> Lang2 k
    Fold2 : (a -> b -> b) -> Vect n a -> (b -> k) -> Lang2 k
    InnerProd2 : Vect n a -> Vect n a -> (a -> k) -> Lang2 k

Functor Lang2 where
    map f (Map2 g v h) = Map2 g v (f . h)
    map f (Fold2 g v h) = Fold2 g v (f . h)
    map f (InnerProd2 v w h) = InnerProd2 v w (f . h)

lmap2 : (a -> b) -> Vect n a -> Free Lang2 (Vect n b)
lmap2 f v = Op (Map2 f v pure)

lfold2 : (a -> b -> b) -> Vect n a -> Free Lang2 b
lfold2 f v = Op (Fold2 f v pure)

linnerprod2 : Num a => Vect n a -> Vect n a -> Free Lang2 a
linnerprod2 v w = Op (InnerProd2 v w pure)

lvec2 : (n : Nat) -> a -> Free Lang2 (Vect n a)
lvec2 n x = Var (replicate n x)

test : Free Lang2 Int
test = do
    u <- lvec2 8 5
    v <- lmap2 (+5) u
    w <- lvec2 8 3
    x <- linnerprod2 v w
    pure x
