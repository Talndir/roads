module RubyUntyped

import AE
import Ruby
import RBS
import Data.Vect

Ruby : Type
Ruby = Free RComb Block

infixl 3 <:>
(<:>) : RComb -< f => Free f a -> Free f a -> Free f a
(q <:> r) = ins (Seq q r)

infixl 3 <<:>
(<<:>) : RComb -< f => Free f a -> Free f a -> Free f a
(q <<:> r) = ins (SeqL q r)

infixl 3 <:>>
(<:>>) : RComb -< f => Free f a -> Free f a -> Free f a
(q <:>> r) = ins (SeqR q r)

infixl 3 <|>
(<|>) : RComb -< f => Free f a -> Free f a -> Free f a
(q <|> r) = ins (Par q r)

inv : RComb -< f => Free f a -> Free f a
inv q = ins (Inv q)

infixl 3 >>
(>>) : RComb -< f => Free f a -> Free f a -> Free f a
(q >> r) = ins (Bes q r)

infixl 3 ^^
(^^) : RComb -< f => Free f a -> Free f a -> Free f a
(q ^^ r) = ins (Bel q r)

loop : RComb -< f => Free f a -> Free f a
loop q = ins (Loop q)

id : Free f Block
id = build 1 1 "id"

fst : RComb -< f => Free f Block -> Free f Block
fst q = q <|> id

snd : RComb -< f => Free f Block -> Free f Block
snd r = id <|> r

-- Priority Queue

fork : Ruby
fork = build 1 2 "fork"
outl : Ruby
outl = build 2 1 "outl"
outr : Ruby
outr = build 2 1 "outr"
rsh : Ruby
rsh = Var $ Bloc (T [V, T [V, V]], T [T [V, V], V]) "rsh"
mux : Ruby
mux = Var $ Bloc (T [T [V, V], V], V) "mux"
max : Ruby
max = build 2 1 "max"
min : Ruby
min = build 2 1 "min"
latch : Ruby
latch = build 1 1 "D"

repeat : Nat -> Ruby -> Ruby
repeat Z     _ = id
repeat (S Z) q = q
repeat (S n) q = repeat n q <:> q

fork2 : Ruby
fork2 = inv (outl) <:> (inv fork <|> fork) <:> rsh

mux2 : Ruby
mux2 = fork <:> (mux <|> outl)

sort2 : Ruby
sort2 = fork <:> (min <|> max)

pqcell : Ruby
pqcell = loop ((sort2 ^^ mux2) ^^ ((id <|> latch) <:> fork2))

pq : Ruby
pq = repeat 4 pqcell
