module RubyIndexed

import AE
import State
import Indexed
import IAE
import Tuple
import Data.String

-- Ruby

data RComb : (k : Typ -> Type) -> Typ -> Type where
    Seq : {a,b,c : Tuple} -> k (a, b) -> k (b, c) -> RComb k (a, c)
    SeqL : {a,b,c,d : Tuple} -> k (a, b) -> k (T [b, c], d) -> RComb k (T [a, c], d)
    SeqR : {a,b,c,d : Tuple} -> k (a, T [b, c]) -> k (c, d) -> RComb k (a, T [b, d])
    Par : {a,b,c,d : Tuple} -> k (a, b) -> k (c, d) -> RComb k (T [a, c], T [b, d])
    Inv : {a,b : Tuple} -> k (a, b) -> RComb k (b, a)
    Bes : {a,b,c,d,e,f,v : Tuple} -> k (T [a, b], T [d, v]) -> k (T [v, c], T [e, f]) -> RComb k (T [a, T [b, c]], T [T [d, e], f])
    Bel : {a,b,c,d,e,f,v : Tuple} -> k (T [a, v], T [d, e]) -> k (T [b, c], T [v, f]) -> RComb k (T [T [a, b], c], T [d, T [e, f]])
    Loop : {a,b,c : Tuple} -> k (T [a, b], T [b, c]) -> RComb k (a, c)

IFunctor RComb where
    imap f (Seq q r) = Seq (f q) (f r)
    imap f (SeqL q r) = SeqL (f q) (f r)
    imap f (SeqR q r) = SeqR (f q) (f r)
    imap f (Par q r) = Par (f q) (f r)
    imap f (Inv q) = Inv (f q)
    imap f (Bes q r) = Bes (f q) (f r)
    imap f (Bel q r) = Bel (f q) (f r)
    imap f (Loop q) = Loop (f q)


Ruby : Typ -> Type
Ruby = IFree RComb (Const Typ String)

infixl 3 <:>
(<:>) : {a,b,c : Tuple} -> Ruby (a, b) -> Ruby (b, c) -> Ruby (a, c)
(q <:> r) = Do (Seq q r)

infixl 3 <<:>
(<<:>) : {a,b,c,d : Tuple} -> Ruby (a, b) -> Ruby (T [b, c], d) -> Ruby (T [a, c], d)
(q <<:> r) = Do (SeqL q r)

infixl 3 <:>>
(<:>>) : {a,b,c,d : Tuple} -> Ruby (a, T [b, c]) -> Ruby (c, d) -> Ruby (a, T [b, d])
(q <:>> r) = Do (SeqR q r)

infixl 3 <|>
(<|>) : {a,b,c,d : Tuple} -> Ruby (a, b) -> Ruby (c, d) -> Ruby (T [a, c], T [b, d])
(q <|> r) = Do (Par q r)

inv : {a,b : Tuple} -> Ruby (a, b) -> Ruby (b, a)
inv q = Do (Inv q)

infixl 3 >>
(>>) :  {a,b,c,d,e,f,v : Tuple}
     -> Ruby (T [a, b], T [d, v])
     -> Ruby (T [v, c], T [e, f])
     -> Ruby (T [a, T [b, c]], T [T [d, e], f])
(q >> r) = Do (Bes q r)

infixl 3 ^^
(^^) :  {a,b,c,d,e,f,v : Tuple}
     -> Ruby (T [a, v], T [d, e])
     -> Ruby (T [b, c], T [v, f])
     -> Ruby (T [T [a, b], c], T [d, T [e, f]])
(q ^^ r) = Do (Bel q r)

loop : {a,b,c : Tuple} -> Ruby (T [a, b], T [b, c]) -> Ruby (a, c)
loop q = Do (Loop q)

id : {u : Tuple} -> Ruby (u, u)
id = Gen "id"

repeat : Nat -> {u : Tuple} -> Ruby (u, u) -> Ruby (u, u)
repeat Z     _ = id
repeat (S Z) q = q
repeat (S n) q = repeat n q <:> q

-- Priority Queue

fork : {u : Tuple} -> Ruby (u, T [u, u])
fork = Gen "fork"

outl : {u : Tuple} -> {v : Tuple} -> Ruby (T [u, v], u)
outl = Gen "outl"

outr : {u : Tuple} -> {v : Tuple} -> Ruby (T [u, v], v)
outr = Gen "outr"

rsh : {u : Tuple} -> {v : Tuple} -> {w : Tuple} -> Ruby (T [u, T [v, w]], T [T [u, v], w])
rsh = Gen "rsh"

mux : {u : Tuple} -> Ruby (T [W, T [u, u]], u)
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

SRBS : Typ -> Type
SRBS (a, b) = (x : shape a Nat) -> (y : shape b Nat) -> Free (State Nat) (Ruby (fst x, fst y))

inc : Num s => Free (State s) s
inc = Prelude.do
    v <- get
    put (v + 1)
    pure (v + 1)

seqD : Monad m => {f : a -> b -> Type} -> ((x : a) -> m (y : b ** f x y)) -> (xs : Vect n a) -> m (DVect f xs)
seqD f Nil = pure Nil
seqD f (x :: xs) = do
    y <- f x
    ys <- seqD f xs
    pure (y :: ys)

new : (x : Tuple) -> Free (State Nat) (shape x Nat)
new (V _) = do
    x <- inc
    pure (V x ** Refl)
new (T xs) = do
    ys <- seqD new xs
    pure $ fst (makeT ys)

comb : x1 = x2 -> y1 = y2 -> (x1, y1) = (x2, y2)
comb Refl Refl = Refl

Rx : Typ -> Type
Rx x = Free (State Nat) (Ruby x)

welp : {xs : Vect n (Rose Nat)} -> {ys : Vect m (Rose Nat)}
    -> SRBS (T xs, T ys) -> (x : Dv xs Nat) -> (y : Dv ys Nat)
    -> Rx (T (extract x), T (extract y))
welp q x y = let (x' ** px) = makeT x in let (y' ** py) = makeT y in replace {p=Rx} (comb px py) (q x' y')

welp1x : {xs : Rose Nat} -> {ys : Vect m (Rose Nat)}
      -> SRBS (xs, T ys) -> (x : shape xs Nat) -> (y : Dv ys Nat)
      -> Rx (fst x, T (extract y))
welp1x q x y = let (y' ** py) = makeT y in replace {p=Rx} (comb Refl py) (q x y')

welpx1 : {xs : Vect n (Rose Nat)} -> {ys : Rose Nat}
      -> SRBS (T xs, ys) -> (x : Dv xs Nat) -> (y : shape ys Nat)
      -> Rx (T (extract x), fst y)
welpx1 q x y = let (x' ** px) = makeT x in replace {p=Rx} (comb px Refl) (q x' y)

err1x : (x : Rose a) -> (xs : Vect n (Rose a))
     -> (v : shape (T [x, T xs]) b)
     -> (ys : (shape x b, Dv xs b) ** fst v = T [fst (fst ys), T (extract (snd ys))])
err1x x xs (T [r, T rs] ** pf) =
    let ([x', t] ** px) = extractT'' [x, T xs] (T  [r, T rs] ** pf) in
    let (xs' ** pxs) = extractT'' xs t in
    ((x', xs') ** rewrite sym pxs in px)

errx1 : (xs : Vect n (Rose a)) -> (x : Rose a)
     -> (v : shape (T [T xs, x]) b)
     -> (ys : (Dv xs b, shape x b) ** fst v = T [T (extract (fst ys)), fst (snd ys)])
errx1 xs x (T [T rs, r] ** pf) =
    let ([t, x'] ** px) = extractT'' [T xs, x] (T  [T rs, r] ** pf) in
    let (xs' ** pxs) = extractT'' xs t in
    ((xs', x') ** rewrite sym pxs in px)

gen_names : Const Typ String x -> SRBS x
gen_names (s, ((a, b) ** pf)) = rewrite sym pf in \x => \y => pure (Gen s)

alg_names : RComb SRBS x -> SRBS x
alg_names (Seq {a,b,c} q r) = \x => \y => do
    b' <- new b
    q' <- q x b'
    r' <- r b' y
    pure $ Do (Seq q' r')
alg_names (SeqL {a,b,c,d} q r) = \x => \y => do
    let ([a', c'] ** px) = extractT'' [a, c] x
    b' <- new b
    q' <- q a' b'
    r' <- welpx1 r [b', c'] y
    pure $ Do (rewrite px in SeqL q' r')
alg_names (SeqR {a,b,c,d} q r) = \x => \y => do
    let ([b', d'] ** py) = extractT'' [b, d] y
    c' <- new c
    q' <- welp1x q x [b', c']
    r' <- r c' d'
    pure $ Do (rewrite py in SeqR q' r')
alg_names (Par {a,b,c,d} q r) = \x => \y => do
    let ([a', c'] ** pq) = extractT'' [a, c] x
    let ([b', d'] ** pr) = extractT'' [b, d] y
    q' <- q a' b'
    r' <- r c' d'
    pure $ Do (rewrite pq in rewrite pr in Par q' r')
alg_names (Inv {a,b} q) = \x => \y => do
    q' <- q y x
    pure $ Do (Inv q')
alg_names (Bes {a,b,c,d,e,f,v} q r) = \x => \y => do
    let ((a', [b', c']) ** px) = err1x a [b, c] x
    let (([d', e'], f') ** py) = errx1 [d, e] f y
    v' <- new v
    q' <- welp q [a', b'] [d', v']
    r' <- welp r [v', c'] [e', f']
    pure $ Do (rewrite px in rewrite py in Bes q' r')
alg_names (Bel {a,b,c,d,e,f,v} q r) = \x => \y => do
    let (([a', b'], c') ** px) = errx1 [a, b] c x
    let ((d', [e', f']) ** py) = err1x d [e, f] y
    v' <- new v
    q' <- welp q [a', v'] [d', e']
    r' <- welp r [b', c'] [v', f']
    pure $ Do (rewrite px in rewrite py in Bel q' r')
alg_names (Loop {a,b,c} q) = \x => \y => do
    b' <- new b
    q' <- welp q [x, b'] [b', y]
    pure $ Do (Loop q')

New : (f : Typ -> Type) -> Typ -> Type
New f (a, b) = (y : shape2 (a, b) Nat ** f (fst y))

make_names : {x : Typ} -> Ruby x -> New Ruby x
make_names {x=(a,b)} r = flip handle_state 0 $ do
    a' <- new a
    b' <- new b
    r' <- fold gen_names alg_names r a' b'
    pure (((fst a', fst b') ** (sym (snd a'), sym (snd b'))) ** r')

RBS : Type
RBS = List Block

TRBS : Typ -> Type
TRBS = Const Typ RBS

gen_rbs : Const Typ String x -> TRBS x
gen_rbs (s, (x ** Refl)) = ([Bloc x s], (x ** Refl))

make2 : TRBS a -> TRBS b -> (x : Tuple) -> (y : Tuple) -> TRBS (x, y)
make2 (qs, _) (rs, _) x y = (qs ++ rs, ((x, y) ** Refl))

alg_rbs : RComb TRBS x -> TRBS x
alg_rbs (Seq {a,c} q r) = make2 q r a c
alg_rbs (SeqL {a,c,d} q r) = make2 q r (T [a, c]) d
alg_rbs (SeqR {a,b,d} q r) = make2 q r a (T [b, d])
alg_rbs (Par {a,b,c,d} q r) = make2 q r (T [a, c]) (T [b, d])
alg_rbs (Inv {a,b} (qs, _)) = (qs, ((b, a) ** Refl))
alg_rbs (Bes {a,b,c,d,e,f} q r) = make2 q r (T [a, T [b, c]]) (T [T [d, e], f])
alg_rbs (Bel {a,b,c,d,e,f} q r) = make2 q r (T [T [a, b], c]) (T [d, T [e, f]])
alg_rbs (Loop {a,c} (qs, _)) = (qs, ((a, c) ** Refl))

make_rbs : {x : Typ} -> Ruby x -> TRBS x
make_rbs = fold gen_rbs alg_rbs

compile : {x : Typ} -> Ruby x -> New TRBS x
compile {x=(a, b)} r = let (y ** r') = make_names r in (y ** make_rbs r')

Show (TRBS x) where
    show (bs, ((d, c) ** _)) = title ++ line ++ blocks ++ line ++ dirs ++ wiring ++ inputs where
        blocks, wiring, title, line, dirs, inputs : String
        title = padRight 10 ' ' "Name" ++ padRight 30 ' '"Domain" ++ "Range\n" 
        line = replicate 70 '-' ++ "\n"
        blocks = concatWith "\n" bs ++ "\n"
        dirs = "Directions - ? ~ ?\n"
        wiring = "Wiring - " ++ show d ++ " ~ " ++ show c ++ "\n"
        inputs = "Inputs - ?"
