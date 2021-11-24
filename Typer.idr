module Typer

import AE
import Lambda
import Data.SortedMap

public export
Subst : Type
Subst = TType -> TType

public export
Context : Type
Context = String -> TType

public export
data Typer : (c : Type) -> (k : Type) -> Type where
    Unify : TType -> TType -> (Subst -> k) -> Typer c k
    GetC : (c -> k) -> Typer c k
    PutC : c -> k -> Typer c k
    Fresh : (TType -> k) -> Typer c k

public export
Functor (Typer c) where
    map f (Unify t1 t2 c) = Unify t1 t2 (f . c)
    map f (GetC k) = GetC (f . k)
    map f (PutC s k) = PutC s (f k)
    map f (Fresh k) = Fresh (f . k)

public export
unify : TType -> TType -> Free (Typer c) Subst
unify t1 t2 = Op (Unify t1 t2 pure)

public export
getc : Free (Typer c) c
getc = Op (GetC pure)

public export
putc : c -> Free (Typer c) ()
putc c = Op (PutC c (pure ()))

public export
fresh : Free (Typer c) TType
fresh = Op (Fresh pure)

public export
addTo : Eq a => a -> b -> (a -> b) -> (a -> b)
addTo x p f y = if (y == x) then p else f y

public export
tmap : Subst -> Subst
tmap f (TFree x) = case f (TFree x) of
    TFree x => TFree x
    t => tmap f t
tmap _ (TFixed x) = TFixed x
tmap f (TFunc a b) = TFunc (tmap f a) (tmap f b)

public export
runWith : (c -> c) -> Free (Typer c) a -> Free (Typer c) a
runWith f k = do
    c <- getc
    putc (f c)
    result <- k
    putc c
    pure result

public export
M : Type
M = SortedMap String TType

--public export
M' : Type
M' = M -> M -> (M, M)

gen_vars : (String -> TType) -> Gen String M'
gen_vars f v = \mb, mf => case lookup v mb of
    Just _ => (mb, mf)
    Nothing => (mb, insert v (f v) mf)

alg_vars : (String -> TType) -> Alg Lambda M'
alg_vars f (LLam v k) = \mb, mf => k (insert v (f v) mb) mf
alg_vars f (LApp p q) = \mb, mf => let (mb', mf') = p mb mf in q mb' mf'

public export
extractVars : (String -> TType) -> Free Lambda String -> (M, M)
extractVars f l = handle (gen_vars f) (alg_vars f) l empty empty
