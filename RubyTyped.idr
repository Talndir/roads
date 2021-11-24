module RubyTyped

import AE
import Ruby
import RBS
import Data.List

data Typd : Type -> Typ -> Type where
    Tp : k -> Typd k t

TRuby : Typ -> (Type -> Type) -> Type
TRuby t f = Typd (Free f Block) t

strip : TRuby t f -> Free f Block
strip (Tp c) = c

Ruby : Type -> Type
Ruby = RComb

infixl 3 <:>
(<:>) : RComb -< f  => TRuby (a, b) f 
                    -> TRuby (b, c) f
                    -> TRuby (a, c) f
((Tp q) <:> (Tp r)) = Tp (ins (Seq q r))

infixl 3 <<:>
(<<:>) : RComb -< f => TRuby (a, b) f 
                    -> TRuby (T [b, c], d) f
                    -> TRuby (T [a, c], d) f
((Tp q) <<:> (Tp r)) = Tp (ins (SeqL q r))

infixl 3 <:>>
(<:>>) : RComb -< f => TRuby (a, T [b, c]) f 
                    -> TRuby (c, d) f
                    -> TRuby (a, T [b, d]) f
((Tp q) <:>> (Tp r)) = Tp (ins (SeqR q r))

infixl 3 <|>
(<|>) : RComb -< f  => TRuby (a, b) f
                    -> TRuby (c, d) f
                    -> TRuby (T [a, c], T [b, d]) f
((Tp q) <|> (Tp r)) = Tp (ins (Par q r))

inv : RComb -< f => TRuby (a, b) f -> TRuby (b, a) f
inv (Tp q) = Tp (ins (Inv q))

infixl 3 >>
(>>) : RComb -< f   => TRuby (T [a, b], T [d, x]) f
                    -> TRuby (T [x, c], T [e, g]) f
                    -> TRuby (T [a, T [b, c]], T [T [d, e], g]) f
((Tp q) >> (Tp r)) = Tp (ins (Bes q r))

infixl 3 ^^
(^^) : RComb -< f   => TRuby (T [a, x], T [d, e]) f
                    -> TRuby (T [b, c], T [x, g]) f
                    -> TRuby (T [T [a, b], c], T [d, T [e, g]]) f
((Tp q) ^^ (Tp r)) = Tp (ins (Bel q r))

loop : RComb -< f => TRuby (T [a, b], T [b, c]) f -> TRuby (a, c) f
loop (Tp q) = Tp (ins (Loop q))

build' : (a : Nat) -> (b : Nat) -> String -> TRuby (genTuple a, genTuple b) f
build' a b s = Tp (Var (Bloc (genTuple a, genTuple b) s))

id : {u : Tuple} -> TRuby (u, u) f
id = Tp . Var $ Bloc (u, u) "id"

fst : RComb -< f => TRuby (u, v) f -> TRuby (T [u, V], T [v, V]) f
fst q = q <|> id

snd : RComb -< f => TRuby (u, v) f -> TRuby (T [V, u], T [V, v]) f
snd r = id <|> r

-- Priority Queue

fork : {u : Tuple} -> TRuby (u, T [u, u]) f
fork = Tp . Var $ Bloc (u, T [u, u]) "fork"

outl : {u : Tuple} -> {v : Tuple} -> TRuby (T [u, v], u) f
outl = Tp . Var $ Bloc (T [u, v], u) "outl"

outr : {u : Tuple} -> {v : Tuple} -> TRuby (T [u, v], v) f
outr = Tp . Var $ Bloc (T [u, v], v) "outr"

rsh : {u : Tuple} -> {v : Tuple} -> {w : Tuple} -> TRuby (T [u, T [v, w]], T [T [u, v], w]) f
rsh = Tp . Var $ Bloc (T [u, T [v, w]], T [T [u, v], w]) "rsh"

mux : {u : Tuple} -> TRuby (T [V, T [u, u]], u) f
mux = Tp . Var $ Bloc (T [V, T [u, u]], u) "mux"

max : TRuby (T [V, V], V) f
max = build' 2 1 "max"

min : TRuby (T [V, V], V) f
min = build' 2 1 "min"

latch : TRuby (V, V) f
latch = build' 1 1 "D"

dummy : {u : Tuple} -> String -> TRuby (u, u) f
dummy s = Tp . Var $ Bloc (u, u) s

repeat : Nat -> {u : Tuple} -> TRuby (u, u) Ruby -> TRuby (u, u) Ruby
repeat Z     _ = id
repeat (S Z) q = q
repeat (S n) q = repeat n q <:> q

fork2 : TRuby (T [V, V], T [T [V, V], V]) Ruby
fork2 = inv (outl) <:> (inv fork <|> fork) <:> rsh

mux2 : TRuby (T [V, T [V, V]], T [V, V]) Ruby
mux2 = fork <:> (mux <|> outl)

sort2 : TRuby (T [V, V], T [V, V]) Ruby
sort2 = fork <:> (min <|> max)

pqcell : TRuby (T [T [V, V], V], T [T [V, V], V]) Ruby
pqcell = loop ((sort2 ^^ mux2) ^^ ((id <|> latch) <:> fork2))

pq : TRuby (T [T [V, V], V], T [T [V, V], V]) Ruby
pq = repeat 4 pqcell

comp : TRuby t Ruby -> String
comp = show . compile . strip
