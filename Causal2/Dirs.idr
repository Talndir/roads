module Causal2.Dirs

import public IAE
import public Data.Vect
import public Data.HVect
import Data.Stream

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

data Typ : Type where
    W : Type -> Dir -> Typ
    N : Vect n Typ -> Typ

data Showable : Typ -> Type where
    WShow : Show a => Showable (W a _)
    TShow : {ts : Vect n Typ} -> HVect (map Showable ts) -> Showable (N ts)

Typ' : Type
Typ' = (Typ, Typ)

I, O, IS, OS : Type -> Typ
I x = W x In
O x = W x Out
IS x = W (Stream x) In
OS x = W (Stream x) Out

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

Rep Int where
    rep = 0

Rep a => Rep (Stream a) where
    rep = repeat rep

%hint
makeStream : Data In a => Stream (Data In a)
makeStream @{x} = repeat x

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
        [search y]
        VComplIO : Compl (W t In) (W t Out)
        VComplOI : Compl (W t Out) (W t In)
        TCompl : Compl' xs ys -> Compl (N xs) (N ys)
    
    public export
    data Compl' : (xs : Vect n Typ) -> (ys : Vect n Typ) -> Type where
        [search ys]
        VCompl' : Compl' [] []
        TCompl' : Compl x y -> Compl' xs ys -> Compl' (x :: xs) (y :: ys)

data RComb : (k : Typ' -> Type) -> Typ' -> Type where
    Seq : Compl b b' => k (a, b) -> k (b', c) -> RComb k (a, c)
    Par : k (a, b) -> k (c, d) -> RComb k (N [a, c], N [b, d])
    Inv : k (a, b) -> RComb k (b, a)
    Del : {a, b : Typ} -> Ins a => Compl a b => Data In a -> RComb k (a, b)

IFunctor RComb where
    imap f (Seq q r) = Seq (f q) (f r)
    imap f (Par q r) = Par (f q) (f r)
    imap f (Inv q) = Inv (f q)
    imap f (Del d) = Del d

Ruby : Typ' -> Type
Ruby = IFree RComb Interp

infixl 3 <:>
(<:>) : Ruby (a, b) -> Ruby (b', c) -> Compl b b' => Ruby (a, c)
(q <:> r) = Do (Seq q r)

infixl 3 <|>
(<|>) : Ruby (a, b) -> Ruby (c, d) -> Ruby (N [a, c], N [b, d])
(q <|> r) = Do (Par q r)

inv : Ruby (a, b) -> Ruby (b, a)
inv q = Do (Inv q)

del : {x, y : Typ} -> Ins x => Compl x y => Data In x -> Ruby (x, y)
del d = Do (Del d)

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

fork1 : {x, y : Typ} -> Ins x => Compl x y => Data In x => Data In y => Ruby (x, N [y, y])
fork1 = Ret . Inter $ \(a, B [b, c]) => let t = copy a in (empty a, B [t, t])

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
     => Data In x => Data In y => Data In z => Data In w
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

%hint
outData : {a : Typ} -> Outs a => Data In a
outData @{VOuts} = LIO
outData @{TOuts VOuts'} = B []
outData {a=N(a::as)} @{TOuts (TOuts' t ts)} with (outData @{t})
    _ | y with (outData @{TOuts ts})
     _ | B ys = B (y :: ys)
    
%hint
inData : {a : Typ} -> Ins a => Data Out a
inData @{VIns} = LOI
inData @{TIns VIns'} = B []
inData {a=N(a::as)} @{TIns (TIns' t ts)} with (inData @{t})
    _ | y with (inData @{TIns ts})
     _ | B ys = B (y :: ys)

algDel : {a, b : Typ} -> Ins a => Compl a b => Data In b => Data In a -> Interp (a, b)
algDel d = Inter $ \(x, y) => (empty x, swap d)

alg : RComb Interp x -> Interp x
alg (Seq q r) = algSeq q r
alg (Par q r) = algPar q r
alg (Inv q) = algInv q
alg (Del d) = algDel d

handle : IFree RComb Interp x -> Interp x
handle = fold id alg

run : (Data Out (N [W Int Out, W Int In]), Data Out (N [N [W Int Out, W Int Out], W Int In]))
run = let (Inter f) = handle fork2 in f (B [LIO, LII 10], B [B [LIO, LIO], LII 20])


mux : {x, y : Typ} -> Ins x => Compl x y => Data In x => Data In y
   => Ruby (N [W Bool In, N [x, x]], y)
mux {x, y} = assert_total $ Ret . Inter $ \(B [LII s, B [a, b]], k) =>
    let k' = copy (if s then a else b) in (B [LOI, B [empty a, empty b]], k')

max : Ruby (N [W Int In, W Int In], W Int Out)
max = assert_total $ Ret . Inter $ \(B [LII a, LII b], LIO) => (B [LOI, LOI], LOO $ max a b)

min : Ruby (N [W Int In, W Int In], W Int Out)
min = assert_total $ Ret . Inter $ \(B [LII a, LII b], LIO) => (B [LOI, LOI], LOO $ min a b)

id : {x, y : Typ} -> Compl x y => Data In x => Data In y => Ruby (x, y)
id = Ret . Inter $ \(a, b) => (swap b, swap a)

mux2 : Ruby (N [W Bool In, N [W Int In, W Int In]], N [W Int Out, W Bool Out])
mux2 = fork <:> (mux <|> outl {y=N [W Int In, W Int In]})

sort2 : Ruby (N [W Int In, W Int In], N [W Int Out, W Int Out])
sort2 = fork <:> (min <|> max)


data InterpS : Typ' -> Type where
    InterS : {x, y : Typ} -> Data In x => Data In y
          => (Stream (Data In x, Data In y) -> Stream (Data Out x, Data Out y))
          -> InterpS (x, y)

liftI : Interp a -> InterpS a
liftI (Inter f) = InterS $ \xs => map f xs

algSeqS : Compl b b' => InterpS (a, b) -> InterpS (b', c) -> InterpS (a, c)
algSeqS (InterS f) (InterS g) = InterS $ \rs => 
    let (a0, c0) = unzip rs
        (_, b1) = unzip . f $ zip a0 %search
        (b2, _) = unzip . g $ zip (map swap' b1) c0
        (a, b3) = unzip . f $ zip a0 (map swap' b2) 
        (b4, c) = unzip . g $ zip (map swap' b3) c0
    in zip a c

algParS : InterpS (a, b) -> InterpS (c, d) -> InterpS (N [a, c], N [b, d])
algParS (InterS f) (InterS g) = InterS
    $ map (\((x, u), (y, v)) => (B [x, y], B [u, v]))
    . uncurry zip
    . (\(x, y) => (f x, g y))
    . unzip
    . map (\(B [x, y], B [u, v]) => ((x, u), (y, v)))

algInvS : InterpS (a, b) -> InterpS (b, a)
algInvS (InterS f) = InterS (map swp . f . map swp) where
    swp : (p, q) -> (q, p)
    swp (x, y) = (y, x)

algDelS : {a, b : Typ} -> Ins a => Compl a b => Data In a -> InterpS (a, b)
algDelS d = InterS $ \rs => (inData, swap d) :: map (\(x, y) => (inData, swap x)) rs

algS : RComb InterpS x -> InterpS x
algS (Seq q r) = algSeqS q r
algS (Par q r) = algParS q r
algS (Inv q) = algInvS q
algS (Del d) = algDelS d

handleS : Ruby (a, b) -> InterpS (a, b)
handleS = fold {f=RComb} {c=Interp} {d=InterpS} liftI algS

idS : Stream (Data Out (I Int), Data Out (O Int))
idS = let (InterS f) = handleS id in f (repeat (LII 1, LIO))

run2 : (Data Out (N [W (Stream Int) Out, W (Stream Int) In]), Data Out (N [N [W (Stream Int) Out, W (Stream Int) Out], W (Stream Int) In]))
run2 = let (Inter f) = handle fork2 in f (B [LIO, LII (repeat 10)], B [B [LIO, LIO], LII (repeat 20)])

run3 : Stream (Data Out (N [O Int, I Int]), Data Out (N [N [O Int, O Int], I Int]))
run3 =  let (InterS f) = handleS fork2
        in f $ repeat (B [LIO, LII 10], B [B [LIO, LIO], LII 20])

delayTest : Stream (Data Out (I Int), Data Out (O Int))
delayTest = assert_total $ let (InterS f) = handleS (del (LII (the Int 100)))
            in f $ unfoldr (\x => ((LII x, LIO), x+1)) 0

{-
lift : Typ -> Typ
lift (W a d) = W (Stream a) d
lift (N xs) = N (map lift xs)

liftRep : {a : Typ} -> Data d a => Data d (lift a)
liftRep @{LIO} = LIO
liftRep @{LOI} = LOI
liftRep @{LII x} = LII (repeat x)
liftRep @{LOO x} = LOO (repeat x)
liftRep {a=N []} @{B []} = B []
liftRep {a=N(a::as)} @{B (x :: xs)} with (liftRep @{x})
    _ | y with (liftRep @{B xs})
     _ | B ys = B (y :: ys)

split : {a : Typ} -> Data d (lift a) -> (Data d a, Data d (lift a))
split {a=W a In} (LII (x :: xs)) = (LII x, LII xs)
split {a=W a Out} (LOO (x :: xs)) = (LOO x, LOO xs)
split {a=W _ In} LOI = (LOI, LOI)
split {a=W _ Out} LIO = (LIO, LIO)
split {a=N []} _ = (B [], B [])
split {a=N (a::as)} (B (x :: xs)) with (split {a=a} x)
    _ | (y, z) with (split {a=N as} (B xs))
     _ | (B ys, B zs) = (B (y :: ys), B (z :: zs))

join : {a : Typ} -> Data Out a -> Data Out (lift a) -> Data Out (lift a)
join {a=W _ In} LOI LOI = LOI
join {a=W a Out} (LOO x) (LOO xs) = LOO (x :: xs)
join {a=N []} _ _ = B []
join {a=N (a::as)} (B (x :: xs)) (B (y :: ys)) with (join {a=a} x y)
    _ | z with (join {a=N as} (B xs) (B ys))
     _ | B zs = B (z :: zs)

InterpS : Typ' -> Type
InterpS (a, b) = Interp (lift a, lift b)

liftI : Interp a -> InterpS a
liftI (Inter @{dx} @{dy} f) = Inter @{liftRep} @{liftRep} (\(x, y) =>
    let ((x', xs'), (y', ys')) = (split x, split y)
        (r, s) = f (x', y')
        (Inter f') = liftI (Inter @{dx} @{dy} f)
        (rs, ss) = f' (xs', ys')
    in (join r ?rs, join s ?ss))

%hint
liftCompl : Compl a b => Compl (lift a) (lift b)
liftCompl @{VComplIO} = VComplIO
liftCompl @{VComplOI} = VComplOI
liftCompl @{TCompl VCompl'} = TCompl VCompl'
liftCompl @{TCompl (TCompl' t ts)} with (liftCompl @{t})
    _ | r with (liftCompl @{TCompl ts})
     _ | TCompl rs = TCompl (TCompl' r rs)

%hint
liftIns : Ins a => Ins (lift a)
liftIns @{VIns} = VIns
liftIns @{TIns VIns'} = TIns VIns'
liftIns @{TIns (TIns' t ts)} with (liftIns @{t})
    _ | r with (liftIns @{TIns ts})
     _ | TIns rs = TIns (TIns' r rs)

algDelS : {a, b : Typ} -> Ins a => Compl a b => Data In a -> InterpS (a, b)
algDelS d = Inter @{liftRep} @{liftRep} (\(x, y) =>
    (empty @{liftIns} x, join (swap d) (swap @{liftCompl} x)))

algS : RComb InterpS x -> InterpS x
algS (Seq @{p} q r) = algSeq @{liftCompl} q r
algS (Par q r) = algPar q r
algS (Inv q) = algInv q
algS (Del d) = algDelS d

handleS : Ruby (a, b) -> InterpS (a, b)
handleS = fold {f=RComb} {c=Interp} {d=InterpS} liftI algS

run2 : (Data Out (N [W (Stream Int) Out, W (Stream Int) In]), Data Out (N [N [W (Stream Int) Out, W (Stream Int) Out], W (Stream Int) In]))
run2 = let (Inter f) = handle fork2 in f (B [LIO, LII (repeat 10)], B [B [LIO, LIO], LII (repeat 20)])

run3 : Stream (Data Out (N [O Int, I Int]), Data Out (N [N [O Int, O Int], I Int]))
run3 =  let (Inter f) = handleS (fork2 {x=I Int, y=O Int, z=I Int, w=O Int})
            (l, r) = f (B [LIO, LII (repeat 10)], B [B [LIO, LIO], LII (repeat 20)])
            (p, q) = (unfoldr split l, unfoldr split r)
        in zip p q

run' : (Data Out (lift $ N [O Int, I Int]), Data Out (lift $ N [N [O Int, O Int], I Int]))
run' =  let (Inter f) = handleS (fork2 {x=I Int, y=O Int, z=I Int, w=O Int})
            (l, r) = f (B [LIO, LII (repeat 10)], B [B [LIO, LIO], LII (repeat 20)])
        in (l, r)

err : Stream (Data Out (I Int), Data Out (O Int))
err =   let (Inter f) = handleS (id {x=I Int, y=O Int}) 
            (l, r) = f (LII (repeat 1), LIO)
            (p, q) = (unfoldr split l, unfoldr split r)
        in zip p q
-}