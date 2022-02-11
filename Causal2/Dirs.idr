module Causal2.Dirs

import IAE
import Data.Vect
import Data.HVect

data Rose a = T (Vect n (Rose a)) | V a

Functor Rose where
    map f (V x) = V (f x)
    map f (T rs) = T (map (map f) rs)

TShp : Type
TShp = Rose Type
TShp' : Type
TShp' = (TShp, TShp)

data BRose : TShp -> Type where
    BV : t -> BRose (V t)
    BT : {ts : Vect n (TShp)} -> HVect (map BRose ts) -> BRose (T ts)

(::) : Rose a -> Vect n (Rose a) -> Rose a
t :: ts = T (t :: ts)

tst : BRose ([V Nat, [V String, V Bool]])
tst = BT [BV 1, BT [BV "a", BV True]]

Shp : Type
Shp = Rose Unit

Shp' : Type
Shp' = (Shp, Shp)

data Dir = In | Out

DShp : Type
DShp = Rose Dir
DShp' : Type
DShp' = (DShp, DShp)

I, O : DShp
I = V In
O = V Out

data Typ : Type where
    W : Type -> Dir -> Typ
    N : Vect n Typ -> Typ

data Showable : Typ -> Type where
    WShow : Show a => Showable (W a _)
    TShow : {ts : Vect n Typ} -> HVect (map Showable ts) -> Showable (N ts)

Typ' : Type
Typ' = (Typ, Typ)

data Data : Dir -> Typ -> Type where
    LII : a -> Data In (W a In)
    LOO : a -> Data Out (W a Out)
    LOI : Data Out (W a In)
    LIO : Data In (W a Out)
    B : {xs : Vect n Typ} -> HVect (map (Data d) xs) -> Data d (N xs)

Showable t => Show (Data d t) where
    show @{WShow} (LII x) = show x
    show @{WShow} (LOO x) = show x
    show @{WShow} LOI = "_"
    show @{WShow} LIO = "-"
    show @{TShow ts} (B xs) = "[" ++ show' xs ++ "]" where
        show' : {xs : Vect n Typ} -> HVect (map Showable xs) => HVect (map (Data d) xs) -> String
        show' {xs=[]} [] = ""
        show' {xs=[x]} @{[s]} [v] = show v
        show' {xs=(x::xs)} @{s::ss} (v::vs) = show v ++ ", " ++ show' vs

interface Rep a where
    rep : a

%hint
makeData : Rep a => Data In (W a In)
makeData = LII rep

data Interp : Typ' -> Type where
    Inter : {x, y : Typ} -> Data In x => Data In y
         => ((Data In x, Data In y) -> (Data Out x, Data Out y))
         -> Interp (x, y)

mutual
    public export
    data Ins : Typ -> Type where
        VIns : Ins (W _ In)
        TIns : Ins' xs -> Ins (N xs)
    
    public export
    data Ins' : Vect n Typ -> Type where
        VIns' : Ins' []
        TIns' : Ins x -> Ins' xs -> Ins' (x :: xs)

mutual
    public export
    data Outs : Typ -> Type where
        VOuts : Outs (W _ Out)
        TOuts : Outs' xs -> Outs (N xs)
    
    public export
    data Outs' : Vect n Typ -> Type where
        VOuts' : Outs' []
        TOuts' : Outs x -> Outs' xs -> Outs' (x :: xs)

mutual
    public export
    data Compl : (x : Typ) -> (y : Typ) -> Type where
        [search x, search y]
        VComplIO : Compl (W t In) (W t Out)
        VComplOI : Compl (W t Out) (W t In)
        TCompl : Compl' xs ys -> Compl (N xs) (N ys)
    
    public export
    data Compl' : (xs : Vect n Typ) -> (ys : Vect n Typ) -> Type where
        [search xs, search ys]
        VCompl' : Compl' [] []
        TCompl' : Compl x y -> Compl' xs ys -> Compl' (x :: xs) (y :: ys)

data RComb : (k : Typ' -> Type) -> Typ' -> Type where
    Seq : Compl b b' => k (a, b) -> k (b', c) -> RComb k (a, c)
    Par : k (a, b) -> k (c, d) -> RComb k (N [a, c], N [b, d])
    Inv : k (a, b) -> RComb k (b, a)

IFunctor RComb where
    imap f (Seq q r) = Seq (f q) (f r)
    imap f (Par q r) = Par (f q) (f r)
    imap f (Inv q) = Inv (f q)

Ruby : Typ' -> Type
Ruby = IFree RComb Interp

infixl 3 <:>
(<:>) : Compl b b' => Ruby (a, b) -> Ruby (b', c) -> Ruby (a, c)
(q <:> r) = Do (Seq q r)

infixl 3 <|>
(<|>) : Ruby (a, b) -> Ruby (c, d) -> Ruby (N [a, c], N [b, d])
(q <|> r) = Do (Par q r)

inv : Ruby (a, b) -> Ruby (b, a)
inv q = Do (Inv q)

mutual
    %hint
    export
    complIO : Compl x y -> Ins x -> Outs y
    complIO VComplIO VIns = VOuts
    complIO (TCompl cs) (TIns is) = TOuts (complIO' cs is)

    complIO' : Compl' xs ys -> Ins' xs -> Outs' ys
    complIO' VCompl' VIns' = VOuts'
    complIO' (TCompl' a as) (TIns' b bs) = TOuts' (complIO a b) (complIO' as bs)

mutual
    %hint
    export
    complOI : Compl x y -> Outs y -> Ins x
    complOI VComplIO VOuts = VIns
    complOI (TCompl cs) (TOuts is) = TIns (complOI' cs is)

    complOI' : Compl' xs ys -> Outs' ys -> Ins' xs
    complOI' VCompl' VOuts' = VIns'
    complOI' (TCompl' a as) (TOuts' b bs) = TIns' (complOI a b) (complOI' as bs)

mutual
    %hint
    export
    complCompl : Compl x y -> Compl y x
    complCompl VComplIO = VComplOI
    complCompl VComplOI = VComplIO
    complCompl (TCompl cs) = TCompl (complCompl' cs)

    complCompl' : Compl' xs ys -> Compl' ys xs
    complCompl' VCompl' = VCompl'
    complCompl' (TCompl' a as) = TCompl' (complCompl a) (complCompl' as)

data Fork : (x : Typ) -> (y : Typ) -> (z : Typ) -> Type where
    [search x, search y, search z]
    Fork1 : Compl x y -> Ins x -> Fork x y y
    Fork2 : Compl x y -> Ins x -> Fork y x y
    Fork3 : Compl x y -> Ins x -> Fork y y x

swap : {x, y : Typ} -> Compl x y => Data In x -> Data Out y
swap @{VComplIO} (LII x) = LOO x
swap @{VComplOI} LIO = LOI
swap @{TCompl VCompl'} _ = B []
swap {y=N(y::ys)} @{TCompl (TCompl' t ts)} (B (x :: xs)) with (swap {y=y} x)
    _ | x' with (swap {y=N ys} (B xs))
     _ | B xs' = B (x' :: xs')

swap' : {x, y : Typ} -> Compl x y => Data Out x -> Data In y
swap' @{VComplOI} (LOO x) = LII x
swap' @{VComplIO} LOI = LIO
swap' @{TCompl VCompl'} _ = B []
swap' {y=N(y::ys)} @{TCompl (TCompl' t ts)} (B (x :: xs)) with (swap' {y=y} x)
    _ | x' with (swap' {y=N ys} (B xs))
     _ | B xs' = B (x' :: xs')

copy : {x, y : Typ} -> Ins x => Compl x y => Data In x -> Data Out y
copy = swap

empty : {x : Typ} -> Ins x => Data In x -> Data Out x
empty @{VIns} (LII _) = LOI
empty @{TIns VIns'} _ = B []
empty {x=N(x::xs)} @{TIns (TIns' t ts)} (B (v :: vs)) with (empty {x=x} v)
    _ | v' with (empty {x=N xs} (B vs))
     _ | B vs' = B (v' :: vs')

fork : {x, y, z : Typ} -> Fork x y z => Data In x => Data In y => Data In z => Ruby (x, N [y, z])
fork @{pf} = Ret . Inter $ \(a, B [b, c]) => case pf of
    Fork1 _ _ => let t = copy a in (empty a, B [t, t])
    Fork2 _ _ => let t = copy b in (t, B [empty b, t])
    Fork3 _ _ => let t = copy c in (t, B [t, empty c])

outl : {x, y, z : Typ} -> Ins y => Compl x z
    => Data In x => Data In y => Data In z => Ruby (N [x, y], z)
outl = Ret . Inter $ \(B [a, b], c) => (B [swap c, empty b], swap a)

rsh : {x,y,z,p,q,r : Typ} -> Compl x p => Compl y q => Compl z r
    => Data In x => Data In y => Data In z
    => Data In p => Data In q => Data In r
    => Ruby (N [x, N [y, z]], N [N [p, q], r])
rsh = Ret . Inter $ \(B [a, B [b, c]], B [B [d, e], f]) =>
    (B [swap d, B [swap e, swap f]], B [B [swap a, swap b], swap c])

test1 : {x, y : Typ} -> Compl x y => Ins x => Data In x => Data In y => Ruby (y, N [y, x])
test1 = fork

test2 : {x, y : Typ} -> Compl x y => Ins x => Data In x => Data In y => Ruby (N [y, x], y)
test2 = inv fork

test3 : {x, y, z, w : Typ}
     -> Ins x => Compl x y => Ins z => Compl z w
     => Data In x => Data In y => Data In z => Data In w
     => Ruby (N [N [y, x], w], N [y, N [w, z]])
test3 = (inv fork <|> fork)

test4 : {x, y, z, w : Typ}
     -> Ins x => Compl x y => Ins z => Compl z w
     => Data In x => Data In y => Data In z => Data In w
     => Ruby (N [N [y, x], w], N [N [y, w], z])
test4 = (inv fork <|> fork) <:> rsh

ipi : {x, y, z : Typ} -> Ins y => Compl x z
   => Data In x => Data In y => Data In z
   => Ruby (z, N [x, y])
ipi = inv outl

fork2 : {x, y, z, w : Typ}
     -> Ins x => Compl x y => Ins z => Compl z w
     => Data In x => Data In y => Data In z => Data In w
     => Ruby (N [y, x], N [N [y, w], z])
fork2 = ipi <:> test4

{-
test5 : {x, y, z, w : Typ}
     -> Ins x => Compl x y => Ins z => Compl z w
     => Ruby (N [y, x], N [y, N [w, z]])
test5 = inv outl <:> (inv fork <|> fork)

test6 : {x, y, z, w : Typ}
     -> Ins x => Compl x y => Ins z => Compl z w
     => Ruby (N [y, x], N [N [y, w], z])
test6 = inv outl <:> (inv fork <|> fork) <:> rsh
-}

algSeq : Compl b b' => Interp (a, b) -> Interp (b', c) -> Interp (a, c)
algSeq (Inter f) (Inter g) = Inter $ \(x, y) =>
    let (_, b1) = f (x, %search)
        (b2, _) = g (swap' b1, y)
        (a, b3) = f (x, swap' b2) 
        (b4, c) = g (swap' b3, y) in (a, c)

algPar : Interp (a, b) -> Interp (c, d) -> Interp (N [a, c], N [b, d])
algPar (Inter f) (Inter g) = Inter $ \(B [x, y], B [u, v]) =>
    let (x', u') = f (x, u)
        (y', v') = g (y, v) in (B [x', y'], B [u', v'])

algInv : Interp (a, b) -> Interp (b, a)
algInv (Inter f) = Inter $ \(y, x) => let (x', y') = f (x, y) in (y', x')

alg : RComb Interp x -> Interp x
alg (Seq q r) = algSeq q r
alg (Par q r) = algPar q r
alg (Inv q) = algInv q

handle : IFree RComb Interp x -> Interp x
handle = fold id alg

Rep Int where
    rep = 0

run : (Data Out (N [W Int Out, W Int In]), Data Out (N [N [W Int Out, W Int Out], W Int In]))
run = let (Inter f) = handle fork2 in f (B [LIO, LII 10], B [B [LIO, LIO], LII 20])
