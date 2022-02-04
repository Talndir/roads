module Causal.Constraints

import Data.List
import Data.String
import Causal.Defs

data Com = Same | Comp

Eq Com where
    Same == Same = True
    Comp == Comp = True
    _ == _ = False

Show Com where
    show Same = ""
    show Comp = "~"

swp : Com -> Com
swp Same = Comp
swp Comp = Same

TVar : Type
TVar = (Nat, Com, Maybe Dir)

[showTVar] Show TVar where
    show (x, c, d) = show c ++ show x ++ ":" ++ case d of
        Nothing => "?"
        Just d => show d

Typ : Type
Typ = Rose (Either TVar Dir)

[showTyp] Show Typ where
    show (T xs) = show xs
    show (V (Left x)) = show @{showTVar} x
    show (V (Right x)) = show x

Typ' : Type
Typ' = (Typ, Maybe Dir)

[showTyp'] Show Typ' where
    show (t, Nothing) = show @{showTyp} t ++ " : ?"
    show (t, Just d) = show @{showTyp} t ++ " : " ++ show d

pTyp' : Typ' -> String
pTyp' = show @{showTyp'}

Fork : Type
Fork = (Typ', Typ', Typ')

[showFork] Show Fork where
    show (a, b, c) = "<" ++ pTyp' a ++ ", " ++ pTyp' b ++ ", " ++ pTyp' c ++ ">"

Sub : Type
Sub = Typ' -> Maybe Typ'

combineTVar : TVar -> TVar -> Maybe (Bool, TVar)
combineTVar (x, Same, dx) (y, Same, dy) = case x == y of
    False => Just (False, (x, Same, dx))
    True => case dx of
        Nothing => Just (True, (y, Same, dy))
        Just d => case dy of
            Nothing => Just (True, (y, Same, dx))
            Just d' => case dx == dy of
                False => Nothing
                True => Just (True, (y, Same, dy))
combineTVar _ _ = Nothing

addTVar : TVar -> List TVar -> Maybe (List TVar)
addTVar x (y :: ys) = do
    (r, t) <- combineTVar x y
    case r of
        True => Just (t :: ys)
        False => do
            ts <- addTVar x ys
            Just (y :: ts)
addTVar x [] = Just [x]

getDir : Vect n (Maybe Dir) -> Maybe (Maybe Dir)
getDir (Just x :: xs) = do
    t <- getDir xs
    case t of
        Nothing => Just (Just x)
        Just d => case x == d of
            False => Nothing
            True => Just (Just d)
getDir (Nothing :: xs) = getDir xs
getDir [] = Just Nothing

trav : Applicative f => (a -> f b) -> Vect n a -> f (Vect n b)
trav = traverse

-- Ignores that In(a) implies In(b) if target is T [a, b]
combineTyp : TVar -> Typ -> Maybe Typ'
combineTyp x (T xs) = do
    ys <- trav (combineTyp x) xs
    let (ts, ds) = unzip ys
    d <- getDir ds
    Just (T ts, d)
combineTyp (x, Same, dx) (V (Left (y, cy, dy))) = case x == y of
    False => Just (V (Left (y, cy, dy)), dy)
    True => case cy of
        Same => Just (V (Left (y, Same, dx)), dx)
        Comp => Just (V (Left (y, Comp, map swap dx)), map swap dx)
combineTyp _ (V (Right d)) = Just (V (Right d), Just d)
combineTyp _ _ = Nothing

combineTyp' : TVar -> Typ' -> Maybe Typ'
combineTyp' x (y, Nothing) = combineTyp x y
combineTyp' x (y, Just d) = do
    (y', d') <- combineTyp x y
    case d' of
        Nothing => Just (y', Just d)
        Just t => case d == t of
            True => Just (y', Just d)
            False => Nothing

combineFork : TVar -> Fork -> Maybe Fork
combineFork x (a, b, c) = do
    a' <- combineTyp' x a
    b' <- combineTyp' x b
    c' <- combineTyp' x c
    Just (a', b', c')

applyFork : Sub -> Fork -> Maybe Fork
applyFork s (a, b, c) = do
    a' <- s a
    b' <- s b
    c' <- s c
    Just (a', b', c')

comp : Typ -> Typ
comp = map f where
    f : Either TVar Dir -> Either TVar Dir
    f (Left (x, cx, dx)) = Left (x, swp cx, map swap dx)
    f (Right d) = Right (swap d)

comp' : Typ' -> Typ'
comp' (x, dx) = (comp x, map swap dx)

-- merge a b says b supercedes a
-- Hence if the whole thing is Nothing but one part is In,
-- the whole thing is still nothing (in general)
merge : Maybe Dir -> Maybe Dir -> Maybe (Maybe Dir)
merge x Nothing = Just Nothing
merge Nothing y = Just y
merge (Just x) (Just y) = case x == y of
    True => Just (Just x)
    False => Nothing

orr : Vect n Bool -> Bool
orr (x :: xs) = x || orr xs
orr [] = False

sub' : Nat -> Typ' -> Sub
sub' x (p, dp) (y, dy) = do
    (q, r) <- sub'' x p y
    case r of
        False => Just (y, dy)
        True => merge dp dy >>= \d => Just (q, d)
    where
        sub'' : Nat -> Typ -> Typ -> Maybe (Typ, Bool)
        sub'' x p (V (Left (y, cy, dy))) = case x == y of
            False => Just (V (Left (y, cy, dy)), False)
            True => case cy of
                Comp => sub'' x (comp p) (V (Left (y, Same, map swap dy)))
                Same => Just (p, True)
        sub'' _ _ (V (Right d)) = Just (V (Right d), False)
        sub'' x p (T ys) = do
            ys' <- trav (sub'' x p) ys
            let (zs, vs) = unzip ys'
            Just (T zs, orr vs)

sub : TVar -> Typ' -> Maybe Sub
sub (x, Same, Nothing) p = Just (sub' x p)
sub (x, Same, dx) (p, Nothing) = Just (sub' x (p, dx))
sub (x, Same, dx) (p, dp) = case dx == dp of
    False => Nothing
    True => Just (sub' x (p, dp))
sub (x, Comp, dx) p = sub (x, Same, map swap dx) (comp' p)


test : (Typ', Maybe Typ')
test = (z, sub x y >>= \f => f z) where
    x, w : TVar
    x = (1, Comp, Nothing)
    w = (3, Same, Nothing)
    make : TVar -> Typ
    make = V . Left
    y, z : Typ'
    y = (V (Left (2, Same, Just In)), Just In)
    z = (T [V (Left (1, Same, Nothing)), make w], Nothing)

unify : Typ' -> Typ' -> Maybe (Sub, List TVar)
unify (V (Left (x, cx, dx)), _) (y, dy) = case occurs x y of
    True => Nothing
    False => sub (x, cx, dx) (y, dy) >>= \s => update dx y >>= \u => Just (s, u) where
        occurs : Nat -> Typ -> Bool
        occurs x (V (Right _)) = False
        occurs x (V (Left (y, _, _))) = if x == y then True else False
        occurs x (T ys) = orr (map (occurs x) ys)
        update : Maybe Dir -> Typ -> Maybe (List TVar)
        update Nothing _ = Just []
        update (Just d) (V (Right d')) = case d == d' of
            True => Just []
            False => Nothing
        update (Just d) (V (Left (x, cx, dx))) = case cx of
            Comp => update (Just d) (V (Left (x, Same, map swap dx)))
            Same => case dx of
                Nothing => Just [(x, Same, Just d)]
                Just d' => case d == d' of
                    True => Just []
                    False => Nothing
        update (Just d) (T xs) = trav (update (Just d)) xs >>= Just . concat
unify (V (Right d), _) (V (Right d'), _) = case d == d' of
    True => Just (Just, [])
    False => Nothing
unify (V (Right d), _) y = unify y (V (Right d), Just d)
unify x (V y, d) = unify (V y, d) x
unify (T [], _) (T [], _) = Just (Just, [])
unify (T (x :: xs), dx) (T (y :: ys), dy) = do
    (s, t) <- unify (x, dx) (y, dy)
    ls <- s (T xs, dx)
    rs <- s (T ys, dy)
    (ss, ts) <- unify ls rs
    Just (\k => (s k >>= ss), t ++ ts)
unify (T _, _) (T _, _) = Nothing

checkFork : Fork -> Maybe (Maybe (Sub, List TVar), Bool)
-- Rearrange
checkFork ((a, Nothing), (b, Nothing), (c, Just dc)) = checkFork ((c, Just dc), (a, Nothing), (b, Nothing))
checkFork ((a, Nothing), (b, Just db), (c, Nothing)) = checkFork ((b, Just db), (a, Nothing), (c, Nothing))
checkFork ((a, Nothing), (b, Just db), (c, Just dc)) = checkFork ((c, Just dc), (b, Just db), (a, Nothing))
checkFork ((a, Just da), (b, Nothing), (c, Just dc)) = checkFork ((a, Just da), (c, Just dc), (b, Nothing))
checkFork ((a, da), (b, Just In), (c, dc)) = checkFork ((b, Just In), (a, da), (c, dc))
checkFork ((a, da), (b, db), (c, Just In)) = checkFork ((c, Just In), (a, da), (b, db))
-- Solve
checkFork ((a, Just In), (b, Just Out), (c, Just Out)) = Just (Nothing, True)
checkFork ((a, Just In), (b, Just Out), (c, Nothing)) = unify (c, Nothing) (b, Just Out) >>= \s => Just (Just s, True)
checkFork ((a, Just In), b, c) = unify b (comp a, Just Out) >>= \s => Just (Just s, False)
checkFork ((a, Just Out), (b, Just Out), c) = unify c (comp a, Just In) >>= \s => Just (Just s, True)
checkFork ((a, Just Out), (b, Nothing), (c, Nothing)) = case b == comp c of
    False => unify (b, Nothing) (comp c, Nothing) >>= \s => Just (Just s, False)
    True => Just (Nothing, False)
checkFork ((_, Nothing), (_, Nothing), (_, Nothing)) = Just (Nothing, False)
checkFork _ = Nothing

test2 : String
test2 = p $ do
    (s, _) <- unify x y
    x' <- s x
    y' <- s y
    Just (x', y')
    where
        gen : Nat -> Typ
        gen t = V (Left (t, Same, Nothing))
        x, y : Typ'
        x = (T [T [gen 1, gen 2], gen 3], Nothing)
        y = (T [gen 4, gen 5], Nothing)
        p : Maybe (Typ', Typ') -> String
        p Nothing = "NOTHING"
        p (Just (w, v)) = show @{showTyp'} w ++ " :: " ++ show @{showTyp'} v

Cons : Type
Cons = (List TVar, List Fork)

concatWith : Show a => String -> List a -> String
concatWith _ [] = ""
concatWith _ [x] = show x
concatWith s (x :: xs) = show x ++ s ++ concatWith s xs

[showCons] Show Cons where
    show (vs, fs) = concatWith @{showTVar} "\n" vs
                 ++ "\n\n"
                 ++ concatWith @{showFork} "\n" fs

add : Cons -> TVar -> Maybe Cons
add (vs, fs) t = do
    vs' <- addTVar t vs
    fs' <- traverse (combineFork t) fs
    pure (vs', fs')

addAll : Cons -> List TVar -> Maybe Cons
addAll c (x :: xs) = add c x >>= \c' => addAll c' xs
addAll c [] = Just c

check : List Fork -> Maybe (List Fork, Maybe (Sub, List TVar))
check (x :: xs) = do
    (s, r) <- checkFork x
    case s of
        Nothing => case r of
            True => check xs
            False => check xs >>= \(ys, s') => Just (x :: ys, s')
        Just s' => case r of
            True => Just (xs, Just s')
            False => Just (x :: xs, Just s')
check [] = Just ([], Nothing)

apply : Cons -> (Sub, List TVar) -> Maybe Cons
apply c (s, ts) = do
    (vs, fs) <- addAll c ts
    fs' <- traverse (applyFork s) fs
    pure (vs, fs')

go : Cons -> Maybe Cons
go (vs, fs) = do
    (fs', q) <- check fs
    case q of
        Nothing => pure (vs, fs')
        Just s => apply (vs, fs') s >>= \c => go c

v1, v2, v3 : TVar
v1 = (1, Same, Just In)
v2 = (2, Same, Just Out)
v3 = (3, Same, Nothing)

gen : TVar -> Typ'
gen (x, c, d) = (V (Left (x, c, d)), d)
gen'' : Nat -> TVar
gen'' x = (x, Same, Nothing)
gen' : Nat -> Typ'
gen' x = (V (Left (gen'' x)), Nothing)
genD : Dir -> Typ'
genD d = (V (Right d), Just d)

f1, f2, f3 : Fork
f1 = (gen' 1, gen' 2, genD Out)
f2 = (gen' 1, gen' 3, genD Out)
f3 = (gen' 2, gen' 3, genD Out)

test3 : String
test3 = case go ([gen'' 1, gen'' 2, gen'' 3], [f1, f2]) of
    Nothing => "NOTHING"
    Just r => show @{showCons} r
