module Causal2.Data

import public IAE
import public Data.Vect
import public Data.HVect
import public Data.Stream

public export
data Rose : Type -> Type where
    V : a -> Rose a
    T : Vect n (Rose a) -> Rose a

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
data Typ = TInt | TBool

public export
Eq Typ where
    (==) TInt TInt = True
    (==) TBool TBool = True
    (==) _ _ = False

public export
type : Typ -> Type
type TInt = Int
type TBool = Bool

public export
rep : (t : Typ) -> type t
rep TInt = 0
rep TBool = False

public export
Shp, Shp' : Type
Shp = Rose Typ
Shp' = (Shp, Shp)

public export
data Dir = Left | Right

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

public export
data RComb : (k : DShp' -> Type) -> DShp' -> Type where
    Seq : k (a, b) -> k (b, c) -> RComb k (a, c)
    Par : k (a, b) -> k (c, d) -> RComb k ([a, c], [b, d])
    Inv : {a', b' : DShp} -> Opp a a' => Opp b b' => k (a, b) -> RComb k (b', a')
    Del : {a : DShp} -> Rights a => Data Right a -> RComb k (a, a)

public export
IFunctor RComb where
    imap f (Seq q r) = Seq (f q) (f r)
    imap f (Par q r) = Par (f q) (f r)
    imap f (Inv q) = Inv (f q)
    imap f (Del d) = Del d

infixl 3 <:>
public export
(<:>) : IFree RComb k (a, b) -> IFree RComb k (b, c) -> IFree RComb k (a, c)
(q <:> r) = Do (Seq q r)

infixl 3 <|>
public export
(<|>) : IFree RComb k (a, b) -> IFree RComb k (c, d) -> IFree RComb k ([a, c], [b, d])
(q <|> r) = Do (Par q r)

public export
inv : {a', b' : DShp} -> Opp a a' => Opp b b' => IFree RComb k (a, b) -> IFree RComb k (b', a')
inv q = Do (Inv q)

public export
del : {a : DShp} -> Rights a => Data Right a -> IFree RComb k (a, a)
del d = Do (Del d)
