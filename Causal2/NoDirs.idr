module Causal2.NoDirs

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

data Data : Typ -> Type where
    L : a -> Data (W a _)
    B : {xs : Vect n Typ} -> HVect (map Data xs) -> Data (N xs)

Showable t => Show (Data t) where
    show @{WShow} (L x) = show x
    show @{TShow ts} (B xs) = "[" ++ show' xs ++ "]" where
        show' : {xs : Vect n Typ} -> HVect (map Showable xs) => HVect (map Data xs) -> String
        show' {xs=[]} [] = ""
        show' {xs=[x]} @{[s]} [v] = show v
        show' {xs=(x::xs)} @{s::ss} (v::vs) = show v ++ ", " ++ show' vs

data Interp : Typ' -> Type where
    Inter : {x, y : Typ} -> Data x => Data y => ((Data x, Data y) -> (Data x, Data y)) -> Interp (x, y)

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

merge : Compl x y => Data x -> Data y -> (Data x, Data y)
merge @{VComplIO} (L x) _ = (L x, L x)
merge @{VComplOI} _ (L y) = (L y, L y)
merge @{TCompl VCompl'} _ _ = (B [], B [])
merge @{TCompl (TCompl' t ts)} (B (x::xs)) (B (y::ys)) with (merge x y)
    _ | (x', y') with (merge (B xs) (B ys))
     _ | (B xs', B ys') = (B (x'::xs'), B (y'::ys'))

copy : {x, y : Typ} -> Ins x => Compl x y => Data x -> Data y
copy @{VIns} @{VComplIO} (L x) = L x
copy @{TIns VIns'} @{TCompl VCompl'} _ = B []
copy {y=N(y::ys)} @{TIns (TIns' t ts)} @{TCompl (TCompl' c cs)} (B (x :: xs)) with (copy {y=y} x)
    _ | y' with (copy {y=N ys} (B xs))
     _ | B ys' = B (y' :: ys')

swap : {x, y : Typ} -> Compl x y => Data x -> Data y
swap @{VComplIO} (L x) = L x
swap @{VComplOI} (L x) = L x
swap @{TCompl VCompl'} _ = B []
swap {y=N(y::ys)} @{TCompl (TCompl' t ts)} (B (x :: xs)) with (swap {y=y} x)
    _ | x' with (swap {y=N ys} (B xs))
     _ | B xs' = B (x' :: xs')

%hint
dataHint : (x : Typ) => (y : Typ) => Compl x y -> Data x -> Data y
dataHint @{x} @{y} c v = swap {x, y} @{c} v

rsh : {x,y,z,p,q,r : Typ} -> Compl x p => Compl y q => Compl z r
    => Data x => Data y => Data z
    => Ruby (N [x, N [y, z]], N [N [p, q], r])
rsh = Ret . Inter $ \(B [a, B [b, c]], B [B [d, e], f]) => 
    let ((a', d'), (b', e'), (c', f')) = (merge a d, merge b e, merge c f)
    in (B [a', B [b', c']], B [B [d', e'], f'])

--mux : {x, y : Typ} -> Ins x => Compl x y => Ruby (N [W Bool In, N [x, x]], y)
--mux {x, y} = assert_total (Ret . Inter $ \(B [L s, B [a, b]], k) =>
--    let k' = copy (if s then a else b) in (B [L s, B [a, b]], k'))

outl : {x, y, z : Typ} -> Ins y => Compl x z
    => Data x => Data y => Ruby (N [x, y], z)
outl = Ret . Inter $ \(B [a, b], c) => let (a', c') = merge a c in (B [a', b], c')

data Fork : (x : Typ) -> (y : Typ) -> (z : Typ) -> Type where
    [search x, search y, search z]
    Fork1 : Compl x y -> Ins x -> Fork x y y
    Fork2 : Compl x y -> Ins x -> Fork y x y
    Fork3 : Compl x y -> Ins x -> Fork y y x

fork : {x, y, z : Typ} -> Fork x y z => Data x => Data y => Data z => Ruby (x, N [y, z])
fork @{pf} = Ret . Inter $ \(a, B [b, c]) => case pf of
    Fork1 _ _ => let t = copy a in (a, B [t, t])
    Fork2 _ _ => let t = copy b in (t, B [b, t])
    Fork3 _ _ => let t = copy c in (t, B [t, c])


test1 : {x, y : Typ} -> Compl x y => Ins x => Data x => Ruby (y, N [y, x])
test1 = fork

test2 : {x, y : Typ} -> Compl x y => Ins x => Data x => Ruby (N [y, x], y)
test2 = inv fork

test3 : {x, y, z, w : Typ}
     -> Ins x => Compl x y => Ins z => Compl z w
     => Data x => Data z
     => Ruby (N [N [y, x], w], N [y, N [w, z]])
test3 = (inv fork <|> fork)

test4 : {x, y, z, w : Typ}
     -> Ins x => Compl x y => Ins z => Compl z w
     => Data x => Data z
     => Ruby (N [N [y, x], w], N [N [y, w], z])
test4 = (inv fork <|> fork) <:> rsh

ipi : {x, y, z : Typ} -> Ins y => Compl x z => Data x => Data y => Ruby (z, N [x, y])
ipi = inv outl

fork2 : {x, y, z, w : Typ}
     -> Ins x => Compl x y => Ins z => Compl z w
     => Data x => Data z
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
algSeq (Inter f) (Inter g) = Inter $ \(x, y) => --(x, y)
    let (a1, b1) = f (x, %search) 
        (b2, c1) = g (swap b1, y)
        (a2, b3) = f (a1, swap b2)
        (b4, c2) = g (swap b3, c1) in (a2, c2)

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

%hint
hintInt : Data (W Int d)
hintInt = L 0

run : (Data (N [W Int Out, W Int In]), Data (N [N [W Int Out, W Int Out], W Int In]))
run = let (Inter f) = handle fork2 in f (B [L 1, L 10], B [B [L 2, L 3], L 20])
