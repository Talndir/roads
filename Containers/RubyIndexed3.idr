module Containers.RubyIndexed3

import Effects.Algebraic
import Effects.State
import Effects.Indexed.Functor
import IAE
import Tuple3
import Data.List
import Data.Vect

-- Ruby

NTyp : Type
NTyp = Typ Nat

NTuple : Type
NTuple = Tuple Nat

data RComb : (k : NTyp -> Type) -> NTyp -> Type where
    Seq : {b : NTuple} -> k (a, b) -> k (b, c) -> RComb k (a, c)
    Par : k (a, b) -> k (c, d) -> RComb k (T [a, c], T [b, d])
    Inv : k (a, b) -> RComb k (b, a)
    Bes : k (T [a, b], T [d, x]) -> k (T [x, c], T [e, f]) -> RComb k (T [a, T [b, c]], T [T [d, e], f])
    Bel : k (T [a, x], T [d, e]) -> k (T [b, c], T [x, f]) -> RComb k (T [T [a, b], c], T [d, T [e, f]])
    Loop : k (T [a, b], T [b, c]) -> RComb k (a, c)

IFunctor RComb where
    imap f (Seq q r) = Seq (f q) (f r)
    imap f (Par q r) = Par (f q) (f r)
    imap f (Inv q) = Inv (f q)
    imap f (Bes q r) = Bes (f q) (f r)
    imap f (Bel q r) = Bel (f q) (f r)
    imap f (Loop q) = Loop (f q)

Ruby : Typ Nat -> Type
Ruby = IFree RComb (Const NTyp String)

infixl 3 <:>
(<:>) : {b : NTuple} -> Ruby (a, b) -> Ruby (b, c) -> Ruby (a, c)
(q <:> r) = Do (Seq q r)

infixl 3 <|>
(<|>) : Ruby (a, b) -> Ruby (c, d) -> Ruby (T [a, c], T [b, d])
(q <|> r) = Do (Par q r)

inv : Ruby (a, b) -> Ruby (b, a)
inv q = Do (Inv q)

infixl 3 >>
(>>) :  Ruby (T [a, b], T [d, x])
     -> Ruby (T [x, c], T [e, g])
     -> Ruby (T [a, T [b, c]], T [T [d, e], g])
(q >> r) = Do (Bes q r)

infixl 3 ^^
(^^) :  Ruby (T [a, x], T [d, e])
     -> Ruby (T [b, c], T [x, g])
     -> Ruby (T [T [a, b], c], T [d, T [e, g]])
(q ^^ r) = Do (Bel q r)

loop : Ruby (T [a, b], T [b, c]) -> Ruby (a, c)
loop q = Do (Loop q)

id : {u : NTuple} -> Ruby (u, u)
id = Gen "id"

repeat : Nat -> {u : NTuple} -> Ruby (u, u) -> Ruby (u, u)
repeat Z     _ = id
repeat (S Z) q = q
repeat (S n) q = repeat n q <:> q

-- Priority Queue

fork : {u : NTuple} -> Ruby (u, T [u, u])
fork = Gen "fork"

outl : {u : NTuple} -> {v : NTuple} -> Ruby (T [u, v], u)
outl = Gen "outl"

outr : {u : NTuple} -> {v : NTuple} -> Ruby (T [u, v], v)
outr = Gen "outr"

rsh : {u : NTuple} -> {v : NTuple} -> {w : NTuple} -> Ruby (T [u, T [v, w]], T [T [u, v], w])
rsh = Gen "rsh"

mux : {u : NTuple} -> Ruby (T [W, T [u, u]], u)
mux = Gen "mux"

max : Ruby (T [W, W], W)
max = Gen "max"

min : Ruby (T [W, W], W)
min = Gen "min"

latch : Ruby (W, W)
latch = Gen "D"

fork2 : Ruby (T [W, W], T [T [W, W], W])
fork2 = inv (outl) <:> (inv fork <|> fork) <:> rsh

mux2 : Ruby (T [W, T [W, W]], T [W, W])
mux2 = fork <:> (mux <|> outl)

sort2 : Ruby (T [W, W], T [W, W])
sort2 = fork <:> (min <|> max)

pqcell : Ruby (T [T [W, W], W], T [T [W, W], W])
pqcell = loop ((sort2 ^^ mux2) ^^ ((id <|> latch) <:> fork2))

pq : Ruby (T [T [W, W], W], T [T [W, W], W])
pq = repeat 4 pqcell


-- RBS

SRBS : NTyp -> Type
SRBS t = (x : NTyp) -> Free (State Nat) (Ruby x)

{-
new : NTuple -> Free (State Nat) NTuple
new = ?nw

alg_rbs : RComb SRBS x -> SRBS x
alg_rbs (Seq {b} q r) = \(a, c) => do
    b' <- new b
    q' <- q (a, b')
    r' <- r (b', c)
    pure (Do (Seq q' r'))
alg_rbs (Par q r) = \(T [a, c], T [b, d]) => do
    pure ?w
alg_rbs _ = ?undef

alg_rbs' : (x : NTyp) -> RComb SRBS x -> SRBS x
alg_rbs' (a, c) (Seq {b} q r) = ?u
alg_rbs' (T [a, c], T [b, d]) (Par q r) = ?v
alg_rbs' _ _ = ?und
-}

{-
SRBS : NTyp -> Type
SRBS (x, y) =
    let (n ** (p, v)) = unmake x in
    let (m ** (q, u)) = unmake y in
    (Vect n Nat, Vect m Nat) -> Free (State Nat) (Const NTyp (List (Block Nat)) (x, y))

alg_rbs : RComb SRBS x -> SRBS x
alg_rbs (Seq {b} q r) = ?a
alg_rbs _ = ?undef

inc : Num s => Free (State s) s
inc = do
    v <- get
    put (v + 1)
    pure (v + 1)

iterate : (a -> a) -> a -> (n : Nat) -> Vect n a
iterate f x Z = []
iterate f x (S k) = x :: iterate f (f x) k

new : Rose a -> Rose Nat
new x = let (n ** (p, v)) = unmake x in make (n ** (p, iterate (+1) 0 n))

alg_rbs : RComb SRBS x -> SRBS x
alg_rbs (Seq {b} q r) = \(a,c) => do
    b' <- new b
    q' <- q (a, b)
    r' <- r (b, c)
    pure (q' ++ r')
alg_rbs (Inv q) = q
alg_rbs (Par q r) = \(T [a, c], T [b, d]) => do
    pure []
alg_rbs _ = ?c
-}