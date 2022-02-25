module Containers.RubyIndexed2

import Effects.Algebraic
import Effects.State
import Effects.Indexed.Functor
import IAE
import Tuple2

-- Ruby

data RComb : (k : Typ -> Type) -> Typ -> Type where
    Seq : {b : Tuple} -> k (a, b) -> k (b, c) -> RComb k (a, c)
    SeqL : k (a, b) -> k (T [b, c], d) -> RComb k (T [a, c], d)
    SeqR : k (a, T [b, c]) -> k (c, d) -> RComb k (a, T [b, d])
    Par : k (a, b) -> k (c, d) -> RComb k (T [a, c], T [b, d])
    Inv : k (a, b) -> RComb k (b, a)
    Bes : k (T [a, b], T [d, x]) -> k (T [x, c], T [e, f]) -> RComb k (T [a, T [b, c]], T [T [d, e], f])
    Bel : k (T [a, x], T [d, e]) -> k (T [b, c], T [x, f]) -> RComb k (T [T [a, b], c], T [d, T [e, f]])
    Loop : k (T [a, b], T [b, c]) -> RComb k (a, c)

IFunctor RComb where
    imap f (Seq q r) = Seq (f q) (f r)
    imap f (SeqL q r) = SeqL (f q) (f r)
    imap f (SeqR q r) = SeqR (f q) (f r)
    imap f (Par q r) = Par (f q) (f r)
    imap f (Inv q) = Inv (f q)
    imap f (Bes q r) = Bes (f q) (f r)
    imap f (Bel q r) = Bel (f q) (f r)
    imap f (Loop q) = Loop (f q)

Ind : Typ -> Type
Ind (a, b) = (Vect (holes a) Nat, Vect (holes b) Nat, String)

Ruby : Typ -> Type
Ruby = IFree RComb Ind

iterate : (a -> a) -> a -> (n : Nat) -> Vect n a
iterate f x Z = []
iterate f x (S k) = x :: iterate f (f x) k

blank : (t : Tuple) -> Vect (holes t) Nat
blank t = iterate id 0 (holes t)

make : {a : Tuple} -> {b : Tuple} -> String -> Ruby (a, b)
make {a} {b} s = Ret (blank a, blank b, s)

infixl 3 <:>
(<:>) : {b : Tuple} -> Ruby (a, b) -> Ruby (b, c) -> Ruby (a, c)
(q <:> r) = Do (Seq q r)

infixl 3 <<:>
(<<:>) : Ruby (a, b) -> Ruby (T [b, c], d) -> Ruby (T [a, c], d)
(q <<:> r) = Do (SeqL q r)

infixl 3 <:>>
(<:>>) : Ruby (a, T [b, c]) -> Ruby (c, d) -> Ruby (a, T [b, d])
(q <:>> r) = Do (SeqR q r)

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

id : {u : Tuple} -> Ruby (u, u)
id = make "id"

repeat : Nat -> {u : Tuple} -> Ruby (u, u) -> Ruby (u, u)
repeat Z     _ = id
repeat (S Z) q = q
repeat (S n) q = repeat n q <:> q

-- Priority Queue

fork : {u : Tuple} -> Ruby (u, T [u, u])
fork = make "fork"

outl : {u : Tuple} -> {v : Tuple} -> Ruby (T [u, v], u)
outl = make "outl"

outr : {u : Tuple} -> {v : Tuple} -> Ruby (T [u, v], v)
outr = make "outr"

rsh : {u : Tuple} -> {v : Tuple} -> {w : Tuple} -> Ruby (T [u, T [v, w]], T [T [u, v], w])
rsh = make "rsh"

mux : {u : Tuple} -> Ruby (T [W, T [u, u]], u)
mux = make "mux"

max : Ruby (T [W, W], W)
max = make "max"

min : Ruby (T [W, W], W)
min = make "min"

latch : Ruby (W, W)
latch = make "D"

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

RBS : Typ -> Type
RBS = Const Typ (List Block)

SRBS : Typ -> Type
SRBS x = Typ -> Free (State Nat) (Const Typ (List Block) x)

-- SRBS : Typ -> Type
-- SRBS x = Typ_shape_of_x -> Free (State Nat) (Const Typ (List Block) x)

inc : Num s => Free (State s) s
inc = Prelude.do
    v <- get
    put (v + 1)
    pure (v + 1)

seqM : Monad m => (a -> m b) -> List a -> m (List b)
seqM f Nil = pure Nil
seqM f (x :: xs) = do
    y <- f x
    ys <- seqM f xs
    pure (y :: ys)

-- WRONG
{-
trav : Tuple -> Free (State Nat) Tuple
trav (V _) = do
    v <- inc
    pure (V ())
trav (T xs) = do
    ys <- seqM trav xs
    pure (T ys)

new : Tuple -> Free (State Nat) Tuple
new = trav

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