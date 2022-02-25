module Causal2.Solve

import Data.Nat
import Data.Bool.Xor
import Data.List
import Causal2.Data
import Causal2.Con

split : List (Con Nat) -> (List (Nat, Nat), List Nat, List Nat, List (Nat, Nat))
split (x :: xs) = let (es, ls, rs, cs) = split xs in case x of
    x -= y => case cmp x y of
        CmpLT _ => ((x, y) :: es, ls, rs, cs)
        CmpGT _ => ((y, x) :: es, ls, rs, cs)
        CmpEQ   => (es, ls, rs, cs)
    << x   => (es, x :: ls, rs, cs)
    >> x   => (es, ls, x :: rs, cs)
    x ~~ y => case cmp x y of
        CmpLT _ => (es, ls, rs, (x, y) :: cs)
        CmpGT _ => (es, ls, rs, (y, x) :: cs)
        CmpEQ   => (es, ls, rs, (x, y) :: cs) -- Will fail in makeComps
split [] = ([], [], [], [])

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

update : Fin n -> a -> Vect n a -> Vect n a
update i x vs = updateAt i (const x) vs

-- b = False for Eq, b = True for Compl
makeRels : Bool -> List (Fin n, Fin n) -> Arrange n -> Maybe (Arrange n)
makeRels b xs arr = foldlM f arr (reverse (sort xs)) where
    f : Arrange n -> (Fin n, Fin n) -> Maybe (Arrange n)
    f vs (x, y) = let (x', bx) = index x vs
                      (y', by) = index y vs
                      p = xor b (bx /= by)
                 in case x' == y' of
                    False => Just $ update x' (y', p) vs
                    True => case p of
                        False => Just vs
                        True => Nothing

-- b = False for Left, b = True for Right
makeDirs : Bool -> List (Fin n) -> Assign n -> Maybe (Assign n)
makeDirs b xs ass = foldlM f ass xs where
    f : Assign n -> Fin n -> Maybe (Assign n)
    f vs x = case index x vs of
        Nothing => Just $ update x (Just b) vs
        Just b' => case b == b' of
            True => Just vs
            False => Nothing

combine' : Fin n -> (Fin n, Bool) -> Assign n -> Maybe (Assign n)
combine' k (x, b) vs = case (index k vs, index x vs) of
    (Nothing, r) => Just $ update k (map (xor b) r) vs
    (r, Nothing) => Just $ update x (map (xor b) r) vs
    (Just p, Just q) => case xor b (p == q) of
        True => Just vs
        False => Nothing

combine : {n : Nat} -> Arrange n -> Assign n -> Maybe (Assign n)
combine {n} us vs = foldlM f vs (addIndices us) where
    f : Assign n -> (Fin n, (Fin n, Bool)) -> Maybe (Assign n)
    f x (k, v) = combine' k v x

makeDShp : Bool -> Typ -> (Typ, Dir)
makeDShp False x = (x, Left)
makeDShp True x = (x, Right)

toVect : List a -> (n : Nat ** Vect n a)
toVect (x :: xs) = let (n ** ys) = toVect xs in (S n ** x :: ys)
toVect [] = (0 ** [])

public export
solve : List Typ -> List (Con Nat) -> Maybe (List (Typ, Dir))
solve ts cs = do
    let (es, ls, rs, cs) = split cs
    let (n ** ts') = toVect ts

    es' <- makeFin2 n es
    cs' <- makeFin2 n cs
    f <- makeRels False es' (defArrange n)
    f' <- makeRels True cs' f

    ls' <- makeFin n ls
    rs' <- makeFin n rs
    g <- makeDirs False ls' (defAssign n)
    g' <- makeDirs True rs' g

    g'' <- combine f' g'
    res <- traverse (h ts' f' g'') (addIndices ts')
    pure (toList res) where
        h : Vect n Typ -> Arrange n -> Assign n -> (Fin n, Typ) -> Maybe (Typ, Dir)
        h ts us vs (n, x) =
            let (y, b) = index n us
                t = index y ts
            in case index y vs of
                Nothing => Just $ makeDShp b t
                Just b' => Just $ makeDShp (xor b b') t

testT : List Typ
testT = [TInt, TBool]

testC : List (Con Nat)
testC = [ >> 0, 0 ~~ 1]

test : Maybe (List (Typ, Dir))
test = solve testT testC
