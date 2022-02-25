module Causal2.Data

import public Effects.Indexed.Algebraic
import public Data.Vect
import public Data.HVect
import public Data.Stream

public export
data Rose : Type -> Type where
    V : a -> Rose a
    T : Vect n (Rose a) -> Rose a

public export
Show a => Show (Rose a) where
    show (V x) = show x
    show (T rs) = show rs

public export
Functor Rose where
    map f (V x) = V (f x)
    map f (T xs) = T $ map (map f) xs

public export
Foldable Rose where
    foldr f a (V x) = f x a
    foldr f a (T (x :: xs)) = foldr f (foldr f a (T xs)) x
    foldr f a (T []) = a

public export
Traversable Rose where
    traverse f (V x) = map V (f x)
    traverse f (T xs) = pure T <*> traverse (traverse f) xs

export
vectEq : Eq a => (xs : Vect n a) -> (ys : Vect m a) -> Bool
vectEq (x::xs) (y::ys) = x == y && vectEq xs ys
vectEq [] [] = True
vectEq _ _ = False

public export
Eq a => Eq (Rose a) where
    V x == V y = x == y
    (T xs) == (T ys) = vectEq xs ys
    _ == _ = False

namespace RoseSpace
    public export
    (::) : Rose a -> Vect n (Rose a) -> Rose a
    x :: xs = T (x :: xs)
    public export
    Nil : Rose a
    Nil = T []

public export
data Typ = TInt | TBool | TUnit

public export
Show Typ where
    show TInt = "Int"
    show TBool = "Bool"
    show TUnit = "Unit"

public export
Eq Typ where
    (==) TInt TInt = True
    (==) TBool TBool = True
    (==) TUnit TUnit = True
    (==) _ _ = False

public export
type : Typ -> Type
type TInt = Int
type TBool = Bool
type TUnit = Unit

public export
rep : (t : Typ) -> type t
rep TInt = 0
rep TBool = False
rep TUnit = ()

public export
TShp, TShp' : Type
TShp = Rose Typ
TShp' = (TShp, TShp)

public export
data Dir = Left | Right

public export
Show Dir where
    show Left = "L"
    show Right = "R"

public export
Eq Dir where
    Left == Left = True
    Right == Right = True
    _ == _ = False

public export
swp : Dir -> Dir
swp Left = Right
swp Right = Left

public export
DShp, DShp' : Type
DShp = Rose (Typ, Dir)
DShp' = (DShp, DShp)

public export
data DProp : (Type -> Type) -> DShp -> Type where
    VDProp : p (type a) => DProp p (V (a, _))
    EDProp : DProp p []
    TDProp : DProp p x => DProp p (T xs) => DProp p (T (x :: xs))

public export
L, R, LS, RS : (t : Typ) -> DShp
L t = V (t, Left)
R t = V (t, Right)
--LS t = V (toStream t, Left)
--RS t = V (toStream t, Right)

public export
data Data : Dir -> DShp -> Type where
    LL : type a -> Data Left (L a)
    RR : type a -> Data Right (R a)
    LR : Data Left (R a)
    RL : Data Right (L a)
    Nil : Data d []
    (::) : Data d x -> Data d (T xs) -> Data d (T (x :: xs))

public export
DProp Show t => Show (Data d t) where
    show @{VDProp} (LL x) = show x
    show @{VDProp} (RR x) = show x
    show @{VDProp} LR = ">"
    show @{VDProp} RL = "<"
    show @{EDProp} [] = "[]"
    show @{TDProp} (x :: xs) = "[" ++ show' (x :: xs) ++ "]" where
        show' : DProp Show (T ys) => Data d (T ys) -> String
        show' @{EDProp} [] = ""
        show' @{TDProp} [v] = show v
        show' @{TDProp} (v :: vs) = show v ++ ", " ++ show' vs

public export
gen : {x : DShp} -> {d : Dir} -> Data d x
gen {x=V(t,Left)} {d=Left} = LL $ rep t
gen {x=V(_,Right)} {d=Left} = LR
gen {x=V(_,Left)} {d=Right} = RL
gen {x=V(t,Right)} {d=Right} = RR $ rep t
gen {x=T[]} = []
gen {x=T(x::xs)} = gen :: gen

mutual
    public export
    data Lefts : (x : DShp) -> Type where
        VLefts : Lefts (L a)
        TLefts : Lefts' xs -> Lefts (T xs)
    
    public export
    data Lefts' : Vect n DShp -> Type where
        VLefts' : Lefts' []
        TLefts' : Lefts x -> Lefts' xs -> Lefts' (x :: xs)

mutual
    public export
    data Rights : DShp -> Type where
        VRights : Rights (R a)
        TRights : Rights' xs -> Rights (T xs)
    
    public export
    data Rights' : Vect n DShp -> Type where
        VRights' : Rights' []
        TRights' : Rights x -> Rights' xs -> Rights' (x :: xs)

mutual
    public export
    data Opp : (x : DShp) -> (y : DShp) -> Type where
        [search y]
        VOppLR : Opp (L t) (R t)
        VOppRL : Opp (R t) (L t)
        TOpp : Opp' xs ys -> Opp (T xs) (T ys)
    
    public export
    data Opp' : (xs : Vect n DShp) -> (ys : Vect n DShp) -> Type where
        [search ys]
        VOpp' : Opp' [] []
        TOpp' : Opp x y -> Opp' xs ys -> Opp' (x :: xs) (y :: ys)
