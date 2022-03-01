module Causal2.Typing

import Effects.Algebraic
import Effects.Reader
import Effects.State
import Effects.Error
import Data.List
import Causal2.Data
import Causal2.Con
import Causal2.Dec
import Causal2.Directed
import Causal2.Typed
import Causal2.Solve
import Causal2.Utils
import Causal2.Elab

%language ElabReflection

pi1 : {x, y : DShp} -> Rights y => DBlock ([x, y], x)
pi1 = MkDBlock "pi1" (Inter $ \([a, b], c) => ([c, empty], a))

%runElab makeBlock `{pi1}

public export
ST, ET, RT : Type
ST = (List Typ, List (Con Nat), List (List (Nat, Nat, Nat)))
ET = Unit
RT = (d : DShp' ** DRuby d)

Typer1, Typer2 : Type -> Type
Typer1 = Free (State ST :+: Error ET)
Typer2 = Free (Reader (List (Typ, Dir)) :+: Error ET)

newShp : State ST -< f => TShp -> Free f NShp
newShp t @{p} = traverse g t where
    g : Typ -> Free f Nat
    g x = do
        (xs, ys, zs) <- get @{p}
        put @{p} (x :: xs, ys, zs)
        pure (length xs)

putCon : State ST -< f => Con Nat -> Free f Unit
putCon y @{p} = do
    (xs, ys, zs) <- get @{p}
    put @{p} (xs, y :: ys, zs)

putFork : State ST -< f => List (Nat, Nat, Nat) -> Free f Unit
putFork z @{p} = do
    (xs, ys, zs) <- get @{p}
    put @{p} (xs, ys, z :: zs)

merge : Functor f => State ST -< f => Error ET -< f
     => (Nat -> Nat -> Con Nat) -> NShp -> NShp -> Free f Unit
merge g (V x) (V y) = putCon (g x y)
merge g (T (x :: xs)) (T (y :: ys)) = do
    merge g x y
    merge g (T xs) (T ys)
merge _ (T []) (T []) = pure ()
merge _ _ _ = throw ()

mergeFork : Functor f => State ST -< f => Error ET -< f
         => NShp -> NShp -> NShp -> Free f (List (Nat, Nat, Nat))
mergeFork (V x) (V y) (V z) = pure [(x, y, z)]
mergeFork (T (x :: xs)) (T (y :: ys)) (T (z :: zs)) = do
    u <- mergeFork x y z
    v <- mergeFork (T xs) (T ys) (T zs)
    pure (u ++ v)
mergeFork (T []) (T []) (T []) = pure []
mergeFork _ _ _ = throw ()

newCon : Functor f => State ST -< f => Error ET -< f => Con NShp -> Free f Unit
newCon (<< x) = traverse_ putCon (map (<<) x)
newCon (>> x) = traverse_ putCon (map (>>) x)
newCon (x -= y) = merge (-=) x y
newCon (x ~~ y) = merge (~~) x y
newCon (Fk x y z) = mergeFork x y z >>= putFork

getShp : NShp -> Typer2 DShp
getShp x = do
    ds <- read
    traverse (f ds) x where
    f : List (Typ, Dir) -> Nat -> Typer2 (Typ, Dir)
    f ds n = do
        case inBounds n ds of
            Yes p => pure $ index n ds
            No _ => throw ()

gen_typeIt : TBlock x -> Typer1 (NShp', TShp', Typer2 RT)
gen_typeIt b = do
    l <- newShp (fst b.type)
    r <- newShp (snd b.type)
    let ns = b.vars (l, r)
    traverse_ newCon (b.con ns)
    pure (b.resNat ns, b.type, do
        ds <- traverse getShp ns
        case try (b.con ds) (b.run ds) of
            Nothing => throw ()
            Just b' => pure (b.res ds ** Ret b')
        )

alg_typeIt : TComb (Const (Typer1 (NShp', TShp', Typer2 RT)) TShp') x -> Typer1 (NShp', TShp', Typer2 RT)
alg_typeIt (Seq q r) = do
    ((nqx, nqy), (dqx, dqy), q') <- q
    ((nrx, nry), (drx, dry), r') <- r
    newCon (nqy -= nrx)
    pure ((nqx, nry), (dqx, dry), do
        ((qx, qy) ** qv) <- q'
        ((rx, ry) ** rv) <- r'
        case decEq qy rx of
            No _ => throw ()
            Yes p => pure ((qx, ry) ** qv <:> rewrite p in rv)
        )
alg_typeIt (Par q r) = do
    ((nqx, nqy), (dqx, dqy), q') <- q
    ((nrx, nry), (drx, dry), r') <- r
    pure (([nqx, nrx], [nqy, nry]), ([dqx, drx], [dqy, dry]), do
        ((qx, qy) ** qv) <- q'
        ((rx, ry) ** rv) <- r'
        pure (([qx, rx], [qy, ry]) ** qv <|> rv)
        )
alg_typeIt (Inv q) = do
    ((nx, ny), (dx, dy), q') <- q
    nx' <- newShp dx
    ny' <- newShp dy
    newCon (nx ~~ nx')
    newCon (ny ~~ ny')
    pure ((ny', nx'), (dy, dx), do
        ((x, y) ** v) <- q'
        tx <- getShp nx'
        ty <- getShp ny'
        case (decOpp x tx, decOpp y ty) of
            (Yes p, Yes q) => pure ((ty, tx) ** inv v)
            _ => throw ()
        )
alg_typeIt Del = ?algdel


typeIt : TRuby x -> Typer1 (ST, NShp', Typer2 RT)
typeIt x = do
    (ns, ds, t2) <- fold' gen_typeIt alg_typeIt x
    st <- get
    pure (st, ns, t2)

alg_error : Alg (Error ET) (r -> Either ET a)
alg_error (Throw x) = \_ => Left x

alg_state : Alg (State s) (s -> Either ET a)
alg_state (Get k) = \s => k s s
alg_state (Put s k) = \_ => k s

alg_reader : Alg (Reader r) (r -> Either ET a)
alg_reader (Read k) = \r => k r r

gen : Gen a (r -> Either ET a)
gen x _ = Right x

export
run1 : TRuby x -> Either ET (ST, Typer2 RT)
run1 x = do
    (st, _, t2) <- fold gen (alg_state </> alg_error) (typeIt x) ([], [], [])
    pure (st, t2)

run2 : List (Typ, Dir) -> Typer2 RT -> Either ET RT
run2 ds t2 = fold gen (alg_reader </> alg_error) t2 ds

public export
runAll : TRuby x -> Either ET RT
runAll x = do
    ((ts, rs, fs), t2) <- run1 x
    case solve (reverse ts) rs fs of
        Nothing => Left ()
        Just sols => run2 sols t2

test1 : TRuby (T [V TInt, V TBool], V TInt)
test1 = Ret pi1

test2 : TRuby (T [T [V TInt, V TBool], V TInt], V TInt)
test2 = Ret pi1 <:> Ret pi1
