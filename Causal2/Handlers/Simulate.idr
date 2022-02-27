module Causal2.Handlers.Simulate

import Causal2.Directed
import Causal2.Utils

gen : DBlock x -> Interp x
gen = func

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

alg : DComb Interp x -> Interp x
alg (Seq q r) = algSeq q r
alg (Par q r) = algPar q r
alg (Inv q) = algInv q
alg (Del d) = algDel d

public export
simulate : DRuby x -> Interp x
simulate = fold gen alg
