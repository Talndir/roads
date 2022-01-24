module AE2

import AE
import Data.HVect

data Ann : (f : Type -> Type) -> (hs : Vect n Type) -> (a : Type) -> Type where
    An : (f a) -> HVect hs -> Ann f hs a

Functor f => Functor (Ann f hs) where
    map f (An x an) = An (map f x) an

(Show (f a), Show (HVect hs)) => Show (Ann f hs a) where
    show (An x vs) = show x ++ " : " ++ show vs

AnnFree : (f : Type -> Type) -> (hs : Vect n Type) -> (a : Type) -> Type
AnnFree f hs a = Free (Ann f hs) (a, HVect hs)

getAnn : AnnFree f hs a -> HVect hs
getAnn (Op (An _ t)) = t
getAnn (Var (_, t)) = t

shiftAnn : AnnFree f (b :: hs) a -> AnnFree f hs b
shiftAnn (Var (_, (v :: vs))) = Var (v, vs)
shiftAnn (Op (An op (v :: vs))) = ?w

liftAnn : Functor f => Free f a -> AnnFree f [] a
liftAnn = handle gen alg where
    gen : a -> AnnFree f [] a
    gen x = Var (x, [])
    alg : f (AnnFree f [] a) -> AnnFree f [] a
    alg x = Op (An x [])

hHead : HVect (h :: hs) -> h
hHead (v :: _) = v

AnnGen : Type -> Vect n Type -> Type -> Type
AnnGen a hs b = (a, HVect hs) -> b

AnnAlg : (f : Type -> Type) -> Functor f => Vect n Type -> Type -> Type
AnnAlg f hs b = Ann f hs b -> b

AnnHandler : (f : Type -> Type) -> Functor f => Vect n Type -> Type -> Type -> Type
AnnHandler f hs a b = AnnFree f hs a -> AnnFree f (b :: hs) a

annFold : Functor f => AnnGen a hs b -> AnnAlg f hs b -> AnnHandler f hs a b
annFold gen _ (Var (x, vs)) = Var (x, (gen (x, vs) :: vs))
annFold gen alg (Op (An op vs)) =
    let op' = map (annFold gen alg) op in
    let x = map (hHead . getAnn) op' in
    Op (An op' (alg (An x vs) :: vs))

data Arith : Type -> Type where
    Add : k -> k -> Arith k
    Mul : k -> k -> Arith k

Functor Arith where
    map f (Add x y) = Add (f x) (f y)
    map f (Mul x y) = Mul (f x) (f y)

tst : Free Arith Int
tst = Op (Add (Op (Mul (Var 2) (Var 3))) (Var 7))

gen_tst : AnnGen Int [] Int
gen_tst (x, []) = x

alg_tst : AnnAlg Arith [] Int
alg_tst (An (Add x y) []) = x + y
alg_tst (An (Mul x y) []) = x * y

handle_tst : AnnHandler Arith [] Int Int
handle_tst = annFold gen_tst alg_tst

gen_tst' : AnnGen Int [Int] String
gen_tst' (x, [v]) = show v

alg_tst' : AnnAlg Arith [Int] String
alg_tst' (An (Add x y) [v]) = x ++ " " ++ show v
alg_tst' (An (Mul x y) [v]) = y ++ " " ++ show v

handle_tst' : AnnHandler Arith [Int] Int String
handle_tst' = annFold gen_tst' alg_tst'
    