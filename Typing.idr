module Typing

import Effects.Algebraic
import Lambda
import Typer
import Effects.Annotate
import Data.SortedMap

MTyped : Type
MTyped = Free (Ann Lambda (Maybe TType)) (String, Maybe TType)

Typed : Type
Typed = Free (Ann Lambda TType) (String, TType)

Pair : Type
Pair = (Subst, Typed)

Res : Type
Res = Either String Pair

Typing : Type -> Type
Typing c = Free (Typer c) Pair

gen_mtyped : Gen String MTyped
gen_mtyped x = Var (x, Nothing)

alg_mtyped : Alg Lambda MTyped
alg_mtyped e = Op (An e Nothing)

runMTyped : Handler Lambda String MTyped
runMTyped = handle gen_mtyped alg_mtyped

look : String -> Free (Typer Context) TType
look v = do
    c <- getc
    pure (c v)

gen_typing : Gen (String, Maybe TType) (Typing Context)
gen_typing (v, t') = do
    t <- look v
    s <- case t' of
        Nothing => pure id
        Just u => unify t u
    pure (s, Var (v, s t))

alg_typing : Alg (Ann Lambda (Maybe TType)) (Typing Context)
alg_typing (An (LLam v k) t') = do
    t <- look v
    (s, q) <- runWith (addTo v t) k
    let op = LLam v q
    let ty = TFunc (tmap s t) (getAnn' q)
    s' <- case t' of
        Nothing => pure id
        Just u => unify ty (tmap s u)
    pure (s' . s, Op (An op (tmap s' ty)))
alg_typing (An (LApp p q) t') = do
    (s3, b) <- p
    (s2, a) <- runWith (s3 .) q
    t <- fresh
    s1 <- unify (tmap s2 (getAnn' b)) (TFunc (getAnn' a) t)
    let op = LApp b a
    let ty = tmap s1 t
    let s = s1 . s2 . s3
    s' <- case t' of
        Nothing => pure id
        Just u => unify ty (tmap s u)
    pure (s' . s, Op (An op (tmap s' ty)))

runTyping : Handler (Ann Lambda (Maybe TType)) (String, Maybe TType) (Typing Context)
runTyping = handle gen_typing alg_typing

gen_typer : Gen Pair (a -> Res)
gen_typer x = \_ => Right x

unify' : TType -> TType -> Either String Subst
unify' (TFree x) t = case ((TFree x) == t) of
    True => pure id
    False => case find x t of
        False => Right $ addTo (TFree x) t id
        True => Left $ "Error: Cannot unify " ++ show (TFree x) ++ " and " ++ show t
        where
            find : String -> TType -> Bool
            find x (TFree y) = x == y
            find x (TFixed y) = x == y
            find x (TFunc a b) = find x a || find x b
unify' t (TFree x) = unify' (TFree x) t
unify' (TFunc a b) (TFunc c d) = do
    s1 <- unify' a c
    s2 <- unify' (s1 b) (s1 d)
    pure (s2 . s1)
unify' (TFixed x) (TFixed y) = case x == y of
    True => Right id 
    False => Left $ "Error: Cannot unify " ++ show (TFixed x) ++ " and " ++ show (TFixed y)
unify' x y = Left $ "Error: Cannot unify " ++ show x ++ " and " ++ show y

alg_typer : (Int -> String) -> Alg (Typer c) ((c, Int) -> Res)
alg_typer _ (Unify t1 t2 k) = \c => do
    s <- unify' t1 t2
    k s c
alg_typer _ (GetC k) = \(c, n) => k c (c, n)
alg_typer _ (PutC c k) = \(_, n) => k (c, n)
alg_typer f (Fresh k) = \(c, m) => k (TFree $ f m) (c, m + 1)

runTyper : Handler (Typer Context) Pair ((Context, Int) -> Res)
runTyper = handle gen_typer (alg_typer show)

test : MTyped
test = Op (An lxx (Just (TFunc (TFixed "B") (TFixed "A")))) where
    tx : TType
    tx = TFree "a"
    lxx : Lambda (Free (Ann Lambda (Maybe TType)) (String, Maybe TType))
    lxx = LLam "x" (Var ("x", Just tx))

natToInt : Nat -> Int
natToInt Z = 0
natToInt (S k) = 1 + natToInt k

getVars : Term String -> (Context, Int)
getVars p = (c, natToInt (length list)) where
    map : SortedMap String TType
    map = let (x, y) = extractVars TFree p in mergeLeft x y
    list : List (String, TType)
    list = Data.SortedMap.toList map
    c : Context
    c = foldr (uncurry addTo) (\x => TFree "UNDEF") list

typeIt : MTyped -> Res
typeIt e = do
    (s, l) <- runTyper (runTyping e) (getVars $ stripAnn' e)
    pure (s, annmap' (tmap s) l)
