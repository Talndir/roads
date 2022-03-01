module Causal2.Solve

import Data.Nat
import Data.Bool.Xor
import Data.List
import Causal2.Data
import Causal2.Con

split : List (Con Nat) -> Maybe (List (Nat, Nat), List Nat, List Nat, List (Nat, Nat))
split (x :: xs) = do
    (es, ls, rs, cs) <- split xs
    case x of
        x -= y => case cmp x y of
            CmpLT _ => pure ((x, y) :: es, ls, rs, cs)
            CmpGT _ => pure ((y, x) :: es, ls, rs, cs)
            CmpEQ   => pure (es, ls, rs, cs)
        << x   => pure (es, x :: ls, rs, cs)
        >> x   => pure (es, ls, x :: rs, cs)
        x ~~ y => case cmp x y of
            CmpLT _ => pure (es, ls, rs, (x, y) :: cs)
            CmpGT _ => pure (es, ls, rs, (y, x) :: cs)
            CmpEQ   => Nothing
        Fk x y z => Nothing
split [] = pure ([], [], [], [])

Arrange, Assign : Nat -> Type
Arrange n = Vect n (Fin n, Bool)
Assign n = Vect n (Maybe Bool)

%hint
lteSame : {n : Nat} -> LTE n n
lteSame {n=Z} = LTEZero
lteSame {n=S k} = LTESucc lteSame

toFin : (k : Nat) -> (n : Nat) -> LTE (S k) n => Fin n
toFin Z (S n) = FZ
toFin (S k) (S n) @{p} = FS $ toFin k n @{fromLteSucc p}

genFins : (k : Nat) -> (n : Nat) -> LTE k n => Vect k (Fin n)
genFins (S k) n @{p} = toFin k n :: genFins k n @{lteSuccLeft p}
genFins Z n = []

addIndices : {n : Nat} -> Vect n a -> Vect n (Fin n, a)
addIndices {n} = zip (reverse (genFins n n))

defArrange : (n : Nat) -> Arrange n
defArrange n = addIndices (replicate n False)

defAssign : (n : Nat) -> Assign n
defAssign n = replicate n Nothing

makeFin : (n : Nat) -> List Nat -> Maybe (List (Fin n))
makeFin n xs = traverse (\x => natToFin x n) xs

makeFin2 : (n : Nat) -> List (Nat, Nat) -> Maybe (List (Fin n, Fin n))
makeFin2 n xs = traverse f xs where
    f : (Nat, Nat) -> Maybe (Fin n, Fin n)
    f (x, y) = do
        x' <- natToFin x n
        y' <- natToFin y n
        pure (x', y')

makeFin3 : (n : Nat) -> List (Nat, Nat, Nat) -> Maybe (List (Fin n, Fin n, Fin n))
makeFin3 n xs = traverse f xs where
    f : (Nat, Nat, Nat) -> Maybe (Fin n, Fin n, Fin n)
    f (x, y, z) = do
        x' <- natToFin x n
        y' <- natToFin y n
        z' <- natToFin z n
        pure (x', y', z')

update : Fin n -> a -> Vect n a -> Vect n a
update i x vs = updateAt i (const x) vs

-- If you're pointing at v then point at (x, b) instead
updateRel : Fin n -> (Fin n, Bool) -> (Fin n, (Fin n, Bool)) -> Maybe (Fin n, Bool)
updateRel v (x, b) (i, (y, b')) = case y == v of
    False => Just (y, b')
    True => let p = b /= b' in case x == i of
        False => Just (x, p)
        True => case p of
            False => Just (x, p)
            True => Nothing

addRel : {n : Nat} -> Bool -> Arrange n -> (Fin n, Fin n) -> Maybe (Arrange n)
addRel b vs (x, y) =
    let (x', bx) = index x vs
        (y', by) = index y vs
        p = xor b (bx /= by)
    in case x' == y' of
            False => traverse (updateRel x' (y', p)) (addIndices $ update x' (y', p) vs)
            True => case p of
                False => Just vs
                True => Nothing

addRelSorted : Bool -> Arrange n -> (Fin n, Fin n) -> Maybe (Arrange n)
addRelSorted b vs (x, y) =
    let (x', bx) = index x vs
        (y', by) = index y vs
        p = xor b (bx /= by)
    in case x' == y' of
            False => Just $ update x' (y', p) vs
            True => case p of
                False => Just vs
                True => Nothing

-- b = False for Eq, b = True for Compl
makeRels : Bool -> List (Fin n, Fin n) -> Arrange n -> Maybe (Arrange n)
makeRels b xs arr = foldlM (addRelSorted b) arr (reverse (sort xs))

addDir : Bool -> Assign n -> Fin n -> Maybe (Assign n)
addDir b vs x = case index x vs of
    Nothing => Just $ update x (Just b) vs
    Just b' => case b == b' of
        True => Just vs
        False => Nothing

-- b = False for Left, b = True for Right
makeDirs : Bool -> List (Fin n) -> Assign n -> Maybe (Assign n)
makeDirs b xs ass = foldlM (addDir b) ass xs

combine' : Fin n -> (Fin n, Bool) -> Assign n -> Maybe (Assign n)
combine' k (x, b) vs = case (index k vs, index x vs) of
    (Nothing, Nothing) => Just $ update k (Just $ xor b False) (update x (Just False) vs)
    (Nothing, r) => Just $ update k (map (xor b) r) vs
    (r, Nothing) => Just $ update x (map (xor b) r) vs
    (Just p, Just q) => case xor b (p == q) of
        True => Just vs
        False => Nothing

combine : {n : Nat} -> Arrange n -> Assign n -> Maybe (Assign n)
combine {n} us vs = foldlM (\x, (k, v) => combine' k v x) vs (addIndices us)

makeDShp : Bool -> Typ -> (Typ, Dir)
makeDShp False x = (x, Left)
makeDShp True x = (x, Right)

toVect : List a -> (n : Nat ** Vect n a)
toVect (x :: xs) = let (n ** ys) = toVect xs in (S n ** x :: ys)
toVect [] = (0 ** [])

tryFork1 : {n : Nat} -> (Arrange n, Assign n) -> (Fin n, Fin n, Fin n) -> Maybe (Arrange n, Assign n)
tryFork1 (us, vs) (x, y, z) = do
    us' <- addRel False us (x, y)
    us'' <- addRel False us' (x, z)
    vs' <- addDir True vs x
    pure (us'', vs')

tryFork2 : {n : Nat} -> (Arrange n, Assign n) -> (Fin n, Fin n, Fin n) -> Maybe (Arrange n, Assign n)
tryFork2 (us, vs) (x, y, z) = do
    us' <- addRel False us (x, y)
    us'' <- addRel True us' (x, z)
    vs' <- addDir True vs z
    pure (us'', vs')

tryFork3 : {n : Nat} -> (Arrange n, Assign n) -> (Fin n, Fin n, Fin n) -> Maybe (Arrange n, Assign n)
tryFork3 as (x, y, z) = tryFork2 as (x, z, y)

tryForks : {n : Nat} -> (Arrange n, Assign n) -> List (List (Fin n, Fin n, Fin n)) -> Maybe (Assign n)
tryForks as (x :: xs) = (foldlM tryFork1 as x >>= flip tryForks xs) <|>
                        (foldlM tryFork2 as x >>= flip tryForks xs) <|>
                        (foldlM tryFork3 as x >>= flip tryForks xs)
tryForks (f, g) [] = combine f g

public export
solve : List Typ -> List (Con Nat) -> List (List (Nat, Nat, Nat)) -> Maybe (List (Typ, Dir))
solve ts cs fs = do
    (es, ls, rs, cs) <- split cs
    let (n ** ts') = toVect ts

    es' <- makeFin2 n es
    cs' <- makeFin2 n cs
    f <- makeRels False es' (defArrange n)
    f' <- makeRels True cs' f

    ls' <- makeFin n ls
    rs' <- makeFin n rs
    g <- makeDirs False ls' (defAssign n)
    g' <- makeDirs True rs' g

    fs' <- traverse (makeFin3 n) fs
    g'' <- tryForks (f', g') fs'

    res <- traverse (h g'') (addIndices ts')
    pure (toList res) where
        h : Assign n -> (Fin n, Typ) -> Maybe (Typ, Dir)
        h vs (n, x) = case index n vs of
            Nothing => Just $ makeDShp False x
            Just b' => Just $ makeDShp b' x

testT : List Typ
testT = [TBool, TBool, TInt, TBool, TBool, TInt, TBool, TBool, TBool, TInt, TInt, TInt, TInt, TInt, TInt, TInt, TInt, TBool, TInt, TInt, TInt, TInt, TBool, TInt, TInt]

testC : List (Con Nat)
testC = [(18 -= 21), (17 -= 20), (13 -= 19), (7 -= 16), (6 -= 15), (5 -= 14), (12 ~~ 15), (11 ~~ 14), (10 ~~ 13), (1 ~~ 9), (0 ~~ 8), (2 ~~ 7), (1 ~~ 6), (0 ~~ 5), >> 2]

testF : List (List (Nat, Nat, Nat))
testF = [[(16, (17, 18))], [(10, (11, 12))]]

test : Maybe (List (Typ, Dir))
test = solve testT testC testF
