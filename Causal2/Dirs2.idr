module Causal2.Dirs2

import Causal2.Data
import Causal2.Utils

--%hint
--makeStream : Data Left a => Stream (Data Left a)
--makeStream @{x} = repeat x

data Interp : DShp' -> Type where
    Inter : {x, y : DShp}
         -> ((Data Right x, Data Left y) -> (Data Left x, Data Right y))
         -> Interp (x, y)

Ruby : DShp' -> Type
Ruby = IFree RComb Interp

data Fork : (x : DShp) -> (y : DShp) -> (z : DShp) -> Type where
    Fork1 : Rights x -> Fork x x x
    Fork2 : Opp x y -> Rights x -> Fork y y x
    Fork3 : Opp x y -> Rights x -> Fork y x y

fork : {x, y, z : DShp} -> Fork x y z => Ruby (x, [y, z])
fork @{pf} = Ret . Inter $ \(a, [b, c]) => case pf of
    Fork1 _   => (empty, [a, a])
    Fork2 _ _ => (b, [empty, copy b])
    Fork3 _ _ => (c, [copy c, empty])

outl : {x, y : DShp} -> Rights y => Ruby ([x, y], x)
outl = Ret . Inter $ \([a, b], c) => ([c, empty], a)

rsh : {x, y, z : DShp} -> Ruby ([x, [y, z]], [[x, y], z])
rsh = Ret . Inter $ \([a, [b, c]], [[d, e], f]) =>
    ([d, [e, f]], [[a, b], c])

test1 : {x, y : DShp} -> Rights x => Opp x y => Ruby (y, [y, x])
test1 = fork

test2 : {x, y : DShp} -> Lefts x => Opp x y => Ruby ([y, x], y)
test2 = inv fork

test3 : {x, y, z, w : DShp} -> Lefts x => Opp x y => Rights z => Opp z w
        => Ruby ([[x, y], w], [y, [z, w]])
test3 = (inv fork <|> fork)

test4 : {x, y, z, w : DShp} -> Lefts x => Opp x y => Rights z => Opp z w
        => Ruby ([[x, y], w], [[y, z], w])
test4 = (inv fork <|> fork) <:> rsh

fork2 : {x, y, z, w : DShp} -> Lefts x => Opp x y => Rights z => Opp z w
        => Ruby ([x, y], [[y, z], w])
fork2 = inv outl <:> test4

algSeq : Interp (a, b) -> Interp (b, c) -> Interp (a, c)
algSeq (Inter {y=b} f) (Inter g) = Inter $ \(x, y) =>
    let (_, b1) = f (x, gen)
        (b2, _) = g (b1, y)
        (a, b3) = f (x, b2) 
        (b4, c) = g (b3, y) in (a, c)

algPar : Interp (a, b) -> Interp (c, d) -> Interp ([a, c], [b, d])
algPar (Inter f) (Inter g) = Inter $ \([x, y], [u, v]) =>
    let (x', u') = f (x, u)
        (y', v') = g (y, v) in ([x', y'], [u', v'])

algInv : {a', b' : DShp} -> Opp a a' => Opp b b' => Interp (a, b) -> Interp (b', a')
algInv (Inter f) = Inter $ \(y, x) => let (x', y') = f (swap x, swap y) in (swap y', swap x')

algDel : {a : DShp} -> Rights a => Data Right a -> Interp (a, a)
algDel d = Inter $ \(x, y) => (empty, x)

alg : RComb Interp x -> Interp x
alg (Seq q r) = algSeq q r
alg (Par q r) = algPar q r
alg (Inv q) = algInv q
alg (Del d) = algDel d

handle : IFree RComb Interp x -> Interp x
handle = fold id alg

run : (Data Left [L TInt, R TInt], Data Right [[R TInt, R TInt], L TInt])
run = let (Inter f) = handle fork2 in f ([RL, RR 10], [[LR, LR], LL 20])
