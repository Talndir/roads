module Basic.RBS

import Effects.Algebraic
import Effects.State
import Basic.Ruby
import Data.List
import Data.String

RBS : Type
RBS = (Typ, List Block)

inc : (Num s, (State s) -< f) => Free f s
inc = do
    v <- get
    put (v + 1)
    pure (v + 1)

seqM : Monad m => (a -> m b) -> Vect n a -> m (Vect n b)
seqM f Nil = pure Nil
seqM f (x :: xs) = do
    y <- f x
    ys <- seqM f xs
    pure (y :: ys)

trav : Tuple -> Free (State Nat) Tuple
trav (V _) = do
    v <- inc
    pure (V v)
trav (T xs) = do
    ys <- seqM trav xs
    pure (T ys)

gen_name : Gen Block (Free (State Nat) Ruby)
gen_name (Bloc (d, c) n) = do
    d' <- trav d
    c' <- trav c
    pure (Var (Bloc (d', c') n))

run1 : Monad m => m (Free f a) -> ((Free f a) -> f (Free f a)) -> m (Free f a)
run1 x con = do
    x' <- x
    pure (Op (con x'))

run2 : Monad m => m (Free f a) -> m (Free f a) -> ((Free f a) -> (Free f a) -> f (Free f a)) -> m (Free f a)
run2 x y con = do
    x' <- x
    y' <- y
    pure (Op (con x' y'))

alg_name : Alg RComb (Free (State Nat) Ruby)
alg_name (Seq q r) = run2 q r Seq
alg_name (Par q r) = run2 q r Par
alg_name (Inv q) = run1 q Inv
alg_name (Bes q r) = run2 q r Bes
alg_name (Bel q r) = run2 q r Bel
alg_name (Loop q) = run1 q Loop
 
public export
make_names : Handler RComb Block Ruby
make_names c = handle_state (handle gen_name alg_name c) 0

gen_rbs : Gen Block RBS
gen_rbs (Bloc (d, c) n) = ((d, c), [Bloc (d, c) n])

wire : Nat -> Nat -> Block
wire x y = Bloc (V x, V y) "id"

errorBlock : List Block
errorBlock = [Bloc (V 0, V 0) "ERROR"]

wires : Tuple -> Tuple -> List Block
wires (V x) (V y) = [wire x y]
wires (T (x :: xs)) (T (y :: ys)) = wires x y ++ wires (T xs) (T ys)
wires (T []) (T []) = []
wires _ _ = errorBlock

alg_rbs : Alg RComb RBS
alg_rbs (Seq ((a, b), q) ((c, d), r)) = ((a, d), q ++ r ++ wires b c)
alg_rbs (Par ((a, b), q) ((c, d), r)) = ((T [a, c], T [b, d]), q ++ r)
alg_rbs (Inv ((a, b), q)) = ((b, a), q)
alg_rbs (Bes ((T [a, b], T [c, d]), q) ((T [e, f], T [g, h]), r))
    = ((T [a, T [b, f]], T [T [c, g], h]), q ++ r ++ wires d h)
alg_rbs (Bel ((T [a, b], T [c, d]), q) ((T [e, f], T [g, h]), r))
    = ((T [T [a, e], f], T [c, T [d, h]]), q ++ r ++ wires b g)
alg_rbs (Loop ((T [a, b], T [c, d]), q)) = ((a, d), q ++ wires b c)
alg_rbs _ = ((V 0, V 0), errorBlock)

public export
handle_rbs : Ruby -> RBS
handle_rbs = handle gen_rbs alg_rbs

public export
Show RBS where
    show ((d, c), bs) = title ++ line ++ blocks ++ line ++ dirs ++ wiring ++ inputs where
        blocks, wiring, title, line, dirs, inputs : String
        title = padRight 10 ' ' "Name" ++ padRight 30 ' '"Domain" ++ "Range\n" 
        line = replicate 70 '-' ++ "\n"
        blocks = concatWith "\n" bs ++ "\n"
        dirs = "Directions - ? ~ ?\n"
        wiring = "Wiring - " ++ show d ++ " ~ " ++ show c ++ "\n"
        inputs = "Inputs - ?"

optim : Block -> List Block
optim (Bloc (a, T [b, c]) "fork") = wires a b ++ wires a c
optim (Bloc (T [a, b], c) "outl") = wires a c
optim (Bloc (T [a, b], c) "outr") = wires b c
optim (Bloc (T [a, T [b, c]], T [T [d, e], f]) "rsh") = wires a d ++ wires b e ++ wires c f
optim x = [x]

public export
applyOptim : RBS -> RBS
applyOptim ((d, c), bs) = ((d, c), concatMap optim bs)

public export
removeId : RBS -> RBS
removeId ((d, c), bs) = remove' ((d, c), sortId bs) where
    sortId : List Block -> List Block
    sortId ((Bloc c "id") :: xs) = (Bloc c "id") :: sortId xs
    sortId (x :: xs) = sortId xs ++ [x]
    sortId Nil = Nil
    mapTuple : (Nat -> Nat) -> Tuple -> Tuple
    mapTuple f (V x) = V (f x)
    mapTuple f (T xs) = T (map (mapTuple f) xs)
    alter : Nat -> Nat -> Tuple -> Tuple
    alter x y = mapTuple (\v => if v == y then x else v)
    alter' : (Tuple -> Tuple) -> Block -> Block
    alter' f (Bloc (d, c) n) = Bloc (f d, f c) n
    remove' : RBS -> RBS
    remove' ((d, c), (Bloc (V a, V b) "id") :: xs)
        = let f = alter a b in remove' ((f d, f c), map (alter' f) xs)
    remove' ((d, c), xs) = ((d, c), xs)

public export
compile : Free RComb Block -> RBS
compile = removeId . applyOptim . handle_rbs . make_names
