module Causal2.Handlers.RBS

import Causal2.Typed
import Effects.Algebraic
import Effects.State
import Causal2.Elab
import Causal2.Typing

%language ElabReflection

Block : Type
Block = (String, NShp')

[showBlock] Show Block where
    show (n, (x, y)) = padRight 10 ' ' n ++ padRight 30 ' ' (show x) ++ show y

RBS : Type
RBS = (NShp', List Block)

RBS' : Type
RBS' = (DShp', RBS)

inc : Num s => (State s) -< f => Free f s
inc = do
    v <- get
    put (v + 1)
    pure v

label : Rose a -> Free (State Nat) NShp
label = traverse (\_ => inc)

gen : TBlock x -> Free (State Nat) RBS
gen b = do
    p <- label (fst b.type)
    q <- label (snd b.type)
    pure ((p, q), [(b.name, (p, q))])

addTo : Eq a => a -> b -> (a -> b) -> (a -> b)
addTo x y f z = if z == x then y else f z

construct : NShp -> NShp -> (Nat -> Nat) -> (Nat -> Nat)
construct (V a) (V b) f = addTo a b f
construct (T (x :: xs)) (T (y :: ys)) f = construct (T xs) (T ys) (construct x y f)
construct _ _ f = f

relabel : (Nat -> Nat) -> List Block -> List Block
relabel f bs = map (\(s, (l, r)) => (s, (map f l, map f r))) bs

alg : TComb (Const (Free (State Nat) RBS) TShp') x -> Free (State Nat) RBS
alg (Seq q r) = do
    ((q1, q2), qs) <- q
    ((r1, r2), rs) <- r
    let f = construct r1 q2 id
    pure ((map f q1, map f r2), relabel f (qs ++ rs))
alg (Par q r) = do
    ((q1, q2), qs) <- q
    ((r1, r2), rs) <- r
    pure (([q1, r1], [q2, r2]), qs ++ rs)
alg (Inv q) = do
    ((q1, q2), qs) <- q
    pure ((q2, q1), qs)
alg Del = do
    l <- inc
    r <- inc
    pure ((V l, V r), [("D", (V l, V r))])

makeNames : TRuby x -> RBS
makeNames x = handle_state (fold' gen alg x) 0

outl : {x, y : DShp} -> Rights y => DBlock ([x, y], x)

%runElab makeBlock `{outl}

rsh : {x, y, z : DShp} -> DBlock ([x, [y, z]], [[x, y], z])

%runElab makeBlock `{rsh}

test2 : TRuby (T [T [V TInt, V TBool], V TInt], V TInt)
test2 = Ret outl <:> Ret outl

[showDShp] Show DShp where
    show (V (_, Left)) = "in"
    show (V (_, Right)) = "out"
    show (T xs) = "<" ++ concatWith @{showDShp} ", " (toList xs) ++ ">"

[showRBS'] Show RBS' where
    show ((p, q), ((d, c), bs)) = title ++ line ++ blocks ++ line ++ dirs ++ wiring ++ inputs where
        blocks, wiring, title, line, dirs, inputs : String
        title = "\n" ++ padRight 10 ' ' "Name" ++ padRight 30 ' '"Domain" ++ "Range\n" 
        line = replicate 70 '-' ++ "\n"
        blocks = concatWith @{showBlock} "\n" bs ++ "\n"
        dirs = "Directions - " ++ show @{showDShp} (map (\(x, y) => (x, swp y)) p) ++ " ~ " ++ show @{showDShp} q ++ "\n"
        wiring = "Wiring - " ++ show d ++ " ~ " ++ show c ++ "\n"
        inputs = "Inputs - ?"

tryMe : TRuby x -> Either Unit String
tryMe x = do
    let rbs = makeNames x
    (d ** _) <- runAll x
    pure $ show @{showRBS'} (d, rbs)
