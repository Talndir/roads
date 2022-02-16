module Causal2.Dirs

import public IAE
import public Data.Vect
import public Data.HVect
import Data.Stream

data Rose a = T (Vect n (Rose a)) | V a

Functor Rose where
    map f (V x) = V (f x)
    map f (T rs) = T (map (map f) rs)

(::) : Rose a -> Vect n (Rose a) -> Rose a
t :: ts = T (t :: ts)

data Dir = In | Out

DShp : Type
DShp = Rose (Type, Dir)
DShp' : Type
DShp' = (DShp, DShp)

data Showable : DShp -> Type where
    WShow : Show a => Showable (V (a, _))
    TShow : {ts : Vect n DShp} -> HVect (map Showable ts) -> Showable (T ts)

I, O, IS, OS : Type -> DShp
I x = V (x, In)
O x = V (x, Out)
IS x = V (Stream x, In)
OS x = V (Stream x, Out)

data Data : Dir -> DShp -> Type where
    LII : a -> Data In (I a)
    LOO : a -> Data Out (O a)
    LOI : Data Out (I a)
    LIO : Data In (O a)
    B : {xs : Vect n DShp} -> HVect (map (Data d) xs) -> Data d (T xs)

Showable t => Show (Data d t) where
    show @{WShow} (LII x) = show x
    show @{WShow} (LOO x) = show x
    show @{WShow} LOI = "_"
    show @{WShow} LIO = "-"
    show @{TShow ts} (B xs) = "[" ++ show' xs ++ "]" where
        show' : {xs : Vect n DShp} -> HVect (map Showable xs) => HVect (map (Data d) xs) -> String
        show' {xs=[]} @{[]} [] = ""
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
makeData : Rep a => Data In (I a)
makeData = LII rep

data Interp : DShp' -> Type where
    Inter : {x, y : DShp} -> Data In x => Data In y
         => ((Data In x, Data In y) -> (Data Out x, Data Out y))
         -> Interp (x, y)

mutual
    public export
    data Ins : (x : DShp) -> Type where
        VIns : Ins (I _)
        TIns : Ins' xs -> Ins (T xs)
    
    public export
    data Ins' : Vect n DShp -> Type where
        VIns' : Ins' []
        TIns' : Ins x -> Ins' xs -> Ins' (x :: xs)

mutual
    public export
    data Outs : DShp -> Type where
        VOuts : Outs (O _)
        TOuts : Outs' xs -> Outs (T xs)
    
    public export
    data Outs' : Vect n DShp -> Type where
        VOuts' : Outs' []
        TOuts' : Outs x -> Outs' xs -> Outs' (x :: xs)

mutual
    public export
    data Compl : (x : DShp) -> (y : DShp) -> Type where
        [search y]
        VComplIO : Compl (I t) (O t)
        VComplOI : Compl (O t) (I t)
        TCompl : Compl' xs ys -> Compl (T xs) (T ys)
    
    public export
    data Compl' : (xs : Vect n DShp) -> (ys : Vect n DShp) -> Type where
        [search ys]
        VCompl' : Compl' [] []
        TCompl' : Compl x y -> Compl' xs ys -> Compl' (x :: xs) (y :: ys)

data RComb : (k : DShp' -> Type) -> DShp' -> Type where
    Seq : Compl b b' => k (a, b) -> k (b', c) -> RComb k (a, c)
    Par : k (a, b) -> k (c, d) -> RComb k ([a, c], [b, d])
    Inv : k (a, b) -> RComb k (b, a)
    Del : {a, b : DShp} -> Ins a => Compl a b => Data In a -> RComb k (a, b)

IFunctor RComb where
    imap f (Seq q r) = Seq (f q) (f r)
    imap f (Par q r) = Par (f q) (f r)
    imap f (Inv q) = Inv (f q)
    imap f (Del d) = Del d

Ruby : DShp' -> Type
Ruby = IFree RComb Interp

infixl 3 <:>
(<:>) : Ruby (a, b) -> Ruby (b', c) -> Compl b b' => Ruby (a, c)
(q <:> r) = Do (Seq q r)

infixl 3 <|>
(<|>) : Ruby (a, b) -> Ruby (c, d) -> Ruby ([a, c], [b, d])
(q <|> r) = Do (Par q r)

inv : Ruby (a, b) -> Ruby (b, a)
inv q = Do (Inv q)

del : {x, y : DShp} -> Ins x => Compl x y => Data In x -> Ruby (x, y)
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

data Fork : (x : DShp) -> (y : DShp) -> (z : DShp) -> Type where
    --[search x]
    Fork1 : Compl x y -> Ins x -> Fork x y y
    Fork2 : Compl x y -> Ins x -> Fork y x y
    Fork3 : Compl x y -> Ins x -> Fork y y x

swap : {x, y : DShp} -> Compl x y => Data In x -> Data Out y
swap {x=V(a,In)} @{VComplIO} (LII x) = LOO x
swap {x=V(a,Out)} @{VComplOI} LIO = LOI
swap {x=T[]} @{TCompl VCompl'} _ = B []
swap {y=T(y::ys)} @{TCompl (TCompl' t ts)} (B (x :: xs)) with (swap {y=y} x)
    _ | x' with (swap {y=T ys} (B xs))
     _ | B xs' = B (x' :: xs')

swap' : {x, y : DShp} -> Compl x y => Data Out x -> Data In y
swap' {x=V(a,Out)} @{VComplOI} (LOO x) = LII x
swap' {x=V(a,In)} @{VComplIO} LOI = LIO
swap' {x=T[]} @{TCompl VCompl'} _ = B []
swap' {y=T(y::ys)} @{TCompl (TCompl' t ts)} (B (x :: xs)) with (swap' {y=y} x)
    _ | x' with (swap' {y=T ys} (B xs))
     _ | B xs' = B (x' :: xs')

copy : {x, y : DShp} -> Ins x => Compl x y => Data In x -> Data Out y
copy = swap

empty : {x : DShp} -> Ins x => Data In x -> Data Out x
empty {x=V(_,In)} @{VIns} (LII _) = LOI
empty {x=T[]} @{TIns VIns'} _ = B []
empty {x=T(x::xs)} @{TIns (TIns' t ts)} (B (v :: vs)) with (empty {x=x} v)
    _ | v' with (empty {x=T xs} (B vs))
     _ | B vs' = B (v' :: vs')

fork : {x, y, z : DShp} -> Fork x y z => Data In x => Data In y => Data In z => Ruby (x, [y, z])
fork @{pf} = Ret . Inter $ \(a, B [b, c]) => case pf of
    Fork1 _ _ => let t = copy a in (empty a, B [t, t])
    Fork2 _ _ => let t = copy b in (t, B [empty b, t])
    Fork3 _ _ => let t = copy c in (t, B [t, empty c])

fork1 : {x, y : DShp} -> Ins x => Compl x y => Data In x => Data In y => Ruby (x, [y, y])
fork1 = Ret . Inter $ \(a, B [b, c]) => let t = copy a in (empty a, B [t, t])

outl : {x, y, z : DShp} -> Ins y => Compl x z
    => Data In x => Data In y => Data In z => Ruby ([x, y], z)
outl = Ret . Inter $ \(B [a, b], c) => (B [swap c, empty b], swap a)

rsh : {x,y,z,p,q,r : DShp} -> Compl x p => Compl y q => Compl z r
    => Data In x => Data In y => Data In z
    => Data In p => Data In q => Data In r
    => Ruby ([x, [y, z]], [[p, q], r])
rsh = Ret . Inter $ \(B [a, B [b, c]], B [B [d, e], f]) =>
    (B [swap d, B [swap e, swap f]], B [B [swap a, swap b], swap c])

lsh : {x,y,z,p,q,r : DShp} -> Compl x p => Compl y q => Compl z r
    => Data In x => Data In y => Data In z
    => Data In p => Data In q => Data In r
    => Ruby ([[p, q], r], [x, [y, z]])
lsh = inv rsh

test1 : {x, y : DShp} -> Compl x y => Ins x => Data In x => Data In y => Ruby (y, [y, x])
test1 = fork

test2 : {x, y : DShp} -> Compl x y => Ins x => Data In x => Data In y => Ruby ([y, x], y)
test2 = inv fork

test3 : {x, y, z, w : DShp}
     -> Ins x => Compl x y => Ins z => Compl z w
     => Data In x => Data In y => Data In z => Data In w
     => Ruby ([[y, x], w], [y, [w, z]])
test3 = (inv fork <|> fork)

test4 : {x, y, z, w : DShp}
     -> Ins x => Compl x y => Ins z => Compl z w
     => Data In x => Data In y => Data In z => Data In w
     => Ruby ([[y, x], w], [[y, w], z])
test4 = (inv fork <|> fork) <:> rsh

ipi : {x, y, z : DShp} -> Ins y => Compl x z
   => Data In x => Data In y => Data In z
   => Ruby (z, [x, y])
ipi = inv outl

fork2 : {x, y, z, w : DShp}
     -> Ins x => Compl x y => Ins z => Compl z w
     => Data In x => Data In y => Data In z => Data In w
     => Ruby ([y, x], [[y, w], z])
fork2 = ipi <:> test4

{-
test5 : {x, y, z, w : DShp}
     -> Ins x => Compl x y => Ins z => Compl z w
     => Data In x => Data In y => Data In z => Data In w
     => Ruby (T [y, x], T [y, T [w, z]])
test5 = inv outl <:> (inv fork <|> fork)

test6 : {x, y, z, w : DShp}
     -> Ins x => Compl x y => Ins z => Compl z w
     => Ruby (T [y, x], T [T [y, w], z])
test6 = inv outl <:> (inv fork <|> fork) <:> rsh
-}

algSeq : Compl b b' => Interp (a, b) -> Interp (b', c) -> Interp (a, c)
algSeq (Inter f) (Inter g) = Inter $ \(x, y) =>
    let (_, b1) = f (x, %search)
        (b2, _) = g (swap' b1, y)
        (a, b3) = f (x, swap' b2) 
        (b4, c) = g (swap' b3, y) in (a, c)

algPar : Interp (a, b) -> Interp (c, d) -> Interp ([a, c], [b, d])
algPar (Inter f) (Inter g) = Inter $ \(B [x, y], B [u, v]) =>
    let (x', u') = f (x, u)
        (y', v') = g (y, v) in (B [x', y'], B [u', v'])

algInv : Interp (a, b) -> Interp (b, a)
algInv (Inter f) = Inter $ \(y, x) => let (x', y') = f (x, y) in (y', x')

%hint
outData : {a : DShp} -> Outs a => Data In a
outData {a=V(_,Out)} @{VOuts} = LIO
outData {a=T[]} @{TOuts VOuts'} = B []
outData {a=T(a::as)} @{TOuts (TOuts' t ts)} with (outData @{t})
    _ | y with (outData @{TOuts ts})
     _ | B ys = B (y :: ys)
    
%hint
inData : {a : DShp} -> Ins a => Data Out a
inData {a=V(_,In)} @{VIns} = LOI
inData {a=T[]} @{TIns VIns'} = B []
inData {a=T(a::as)} @{TIns (TIns' t ts)} with (inData @{t})
    _ | y with (inData @{TIns ts})
     _ | B ys = B (y :: ys)

algDel : {a, b : DShp} -> Ins a => Compl a b => Data In b => Data In a -> Interp (a, b)
algDel d = Inter $ \(x, y) => (empty x, swap d)

alg : RComb Interp x -> Interp x
alg (Seq q r) = algSeq q r
alg (Par q r) = algPar q r
alg (Inv q) = algInv q
alg (Del d) = algDel d

handle : IFree RComb Interp x -> Interp x
handle = fold id alg

run : (Data Out [O Int, I Int], Data Out [[O Int, O Int], I Int])
run = let (Inter f) = handle fork2 in f (B [LIO, LII 10], B [B [LIO, LIO], LII 20])


mux : {x, y : DShp} -> Ins x => Compl x y => Data In x => Data In y
   => Ruby ([I Bool, [x, x]], y)
mux {x, y} = assert_total $ Ret . Inter $ \(B [LII s, B [a, b]], k) =>
    let k' = copy (if s then a else b) in (B [LOI, B [empty a, empty b]], k')

max : Ruby ([I Int, I Int], O Int)
max = assert_total $ Ret . Inter $ \(B [LII a, LII b], LIO) => (B [LOI, LOI], LOO $ max a b)

min : Ruby ([I Int, I Int], O Int)
min = assert_total $ Ret . Inter $ \(B [LII a, LII b], LIO) => (B [LOI, LOI], LOO $ min a b)

id : {x, y : DShp} -> Compl x y => Data In x => Data In y => Ruby (x, y)
id = Ret . Inter $ \(a, b) => (swap b, swap a)

mux2 : Ruby ([I Bool, [I Int, I Int]], [O Int, O Bool])
mux2 = fork <:> (mux <|> outl {y=[I Int, I Int]})

sort2 : Ruby ([I Int, I Int], [O Int, O Int])
sort2 = fork <:> (min <|> max)


data InterpS : DShp' -> Type where
    InterS : {x, y : DShp} -> Data In x => Data In y
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

algParS : InterpS (a, b) -> InterpS (c, d) -> InterpS ([a, c], [b, d])
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

algDelS : {a, b : DShp} -> Ins a => Compl a b => Data In a -> InterpS (a, b)
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

run2 : (Data Out [OS Int, IS Int], Data Out [[OS Int, OS Int], IS Int])
run2 = let (Inter f) = handle fork2 in f (B [LIO, LII (repeat 10)], B [B [LIO, LIO], LII (repeat 20)])

run3 : Stream (Data Out [O Int, I Int], Data Out [[O Int, O Int], I Int])
run3 =  let (InterS f) = handleS fork2
        in f $ repeat (B [LIO, LII 10], B [B [LIO, LIO], LII 20])

delayTest : Stream (Data Out (I Int), Data Out (O Int))
delayTest = assert_total $ let (InterS f) = handleS (del (LII (the Int 100)))
            in f $ unfoldr (\x => ((LII x, LIO), x+1)) 0

fst : {a, b, x, y : DShp} -> Ruby (a, b) -> Compl x y
   => Data In x => Data In y => Ruby ([a, x], [b, y])
fst q = q <|> id

snd : {a, b, x, y : DShp} -> Ruby (x, y) -> Compl a b
   => Data In a => Data In b => Ruby ([a, x], [b, y])
snd r = id <|> r

swp : {x, y, z, w : DShp} -> Compl x y => Compl z w
   => Data In x => Data In y => Data In z => Data In w
   => Ruby ([x, z], [w, y])
swp = Ret . Inter $ \(B [a, c], B [d, b]) =>
    (B [swap b, swap d], B [swap c, swap a])

turn : {x, y : DShp} -> Compl x y => Data In x => Data In y => Ruby (T [], T [x, y])
turn = Ret . Inter $ \(B [], B [a, b]) => (B [], B [swap b, swap a])

loopL : {x, y, z, w : DShp} -> Compl x y => Compl z w
     => Data In x => Data In y => Data In z => Data In w
     => Ruby ([x, z], [w, y]) -> Ruby (x, [[y, w], z])
loopL q = inv outl <:> snd turn <:> rsh <:> fst (q <:> swp) --<:> lsh

loopR : {x, y, z, w : DShp} -> Compl x y => Compl z w
     => Data In x => Data In y => Data In z => Data In w
     => Ruby ([[x, w], z], y)
--loopR = lsh <:> snd (inv turn) <:> (outl)

loop : {x, y, z, w : DShp} -> Compl x y => Compl z w
     => Data In x => Data In y => Data In z => Data In w
     => Ruby ([x, z], [w, y]) -> Ruby (x, y)
--loop q = loop' q <:> 

{-
lift : DShp -> DShp
lift (V a d) = V (Stream a) d
lift (T xs) = T (map lift xs)

liftRep : {a : DShp} -> Data d a => Data d (lift a)
liftRep @{LIO} = LIO
liftRep @{LOI} = LOI
liftRep @{LII x} = LII (repeat x)
liftRep @{LOO x} = LOO (repeat x)
liftRep {a=T []} @{B []} = B []
liftRep {a=T(a::as)} @{B (x :: xs)} with (liftRep @{x})
    _ | y with (liftRep @{B xs})
     _ | B ys = B (y :: ys)

split : {a : DShp} -> Data d (lift a) -> (Data d a, Data d (lift a))
split {a=V a In} (LII (x :: xs)) = (LII x, LII xs)
split {a=V a Out} (LOO (x :: xs)) = (LOO x, LOO xs)
split {a=V _ In} LOI = (LOI, LOI)
split {a=V _ Out} LIO = (LIO, LIO)
split {a=T []} _ = (B [], B [])
split {a=T (a::as)} (B (x :: xs)) with (split {a=a} x)
    _ | (y, z) with (split {a=T as} (B xs))
     _ | (B ys, B zs) = (B (y :: ys), B (z :: zs))

join : {a : DShp} -> Data Out a -> Data Out (lift a) -> Data Out (lift a)
join {a=V _ In} LOI LOI = LOI
join {a=V a Out} (LOO x) (LOO xs) = LOO (x :: xs)
join {a=T []} _ _ = B []
join {a=T (a::as)} (B (x :: xs)) (B (y :: ys)) with (join {a=a} x y)
    _ | z with (join {a=T as} (B xs) (B ys))
     _ | B zs = B (z :: zs)

InterpS : DShp' -> Type
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

algDelS : {a, b : DShp} -> Ins a => Compl a b => Data In a -> InterpS (a, b)
algDelS d = Inter @{liftRep} @{liftRep} (\(x, y) =>
    (empty @{liftIns} x, join (swap d) (swap @{liftCompl} x)))

algS : RComb InterpS x -> InterpS x
algS (Seq @{p} q r) = algSeq @{liftCompl} q r
algS (Par q r) = algPar q r
algS (Inv q) = algInv q
algS (Del d) = algDelS d

handleS : Ruby (a, b) -> InterpS (a, b)
handleS = fold {f=RComb} {c=Interp} {d=InterpS} liftI algS

run2 : (Data Out (T [OS Int, IS Int]), Data Out (T [T [OS Int, OS Int], IS Int]))
run2 = let (Inter f) = handle fork2 in f (B [LIO, LII (repeat 10)], B [B [LIO, LIO], LII (repeat 20)])

run3 : Stream (Data Out (T [O Int, I Int]), Data Out (T [T [O Int, O Int], I Int]))
run3 =  let (Inter f) = handleS (fork2 {x=I Int, y=O Int, z=I Int, w=O Int})
            (l, r) = f (B [LIO, LII (repeat 10)], B [B [LIO, LIO], LII (repeat 20)])
            (p, q) = (unfoldr split l, unfoldr split r)
        in zip p q

run' : (Data Out (lift $ T [O Int, I Int]), Data Out (lift $ T [T [O Int, O Int], I Int]))
run' =  let (Inter f) = handleS (fork2 {x=I Int, y=O Int, z=I Int, w=O Int})
            (l, r) = f (B [LIO, LII (repeat 10)], B [B [LIO, LIO], LII (repeat 20)])
        in (l, r)

err : Stream (Data Out (I Int), Data Out (O Int))
err =   let (Inter f) = handleS (id {x=I Int, y=O Int}) 
            (l, r) = f (LII (repeat 1), LIO)
            (p, q) = (unfoldr split l, unfoldr split r)
        in zip p q
-}
