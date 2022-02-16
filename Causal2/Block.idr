module Causal2.Block

import Decidable.Equality
import Causal2.Data
import Causal2.Utils

downShp : DShp -> Shp
downShp (V (t, _)) = V t
downShp (T xs) = T (map downShp xs)

downShp' : DShp' -> Shp'
downShp' (x, y) = (downShp x, downShp y)

mutual
    record Block0 where
        constructor MkBlock0
        name : String
        up : (y : Shp') -> Maybe (Block1 y)

    record Block1 (x : Shp') where
        constructor MkBlock1
        b0 : Block0
        up : (y : DShp') -> Maybe (Block2 y)

    record Block2 (x : DShp') where
        constructor MkBlock2
        b1 : Block1 (downShp' x)
        f : (Data Right (fst x), Data Left (snd x)) -> (Data Left (fst x), Data Right (snd x))


underT : {xs : Vect n (Rose a)} -> {ys : Vect m (Rose b)} -> T xs = T ys -> xs = ys
underT Refl = Refl

overT : {xs : Vect n (Rose a)} -> {ys : Vect m (Rose b)} -> xs = ys -> T xs = T ys
overT Refl = Refl

underV : V x = V y -> x = y
underV Refl = Refl

vNotEqT : V x = T xs -> Void
vNotEqT Refl impossible

consNotEqNil : Equal {a=Vect (S n) a, b = Vect 0 b} (x :: xs) [] -> Void
consNotEqNil Refl impossible

DecEq a => DecEq (Rose a) where
    decEq (V x) (V y) with (decEq x y)
        decEq (V x) (V x) | Yes Refl = Yes Refl
        _                 | No p = No $ p . underV
    decEq (T []) (T []) = Yes Refl
    decEq (T (x :: xs)) (T (y :: ys)) with (decEq x y)
        _ | No p = No $ p . fst . vectInjective . underT
        decEq (T (x :: xs)) (T (x :: ys)) | Yes Refl with (decEq (T xs) (T ys))
            decEq (T (x :: xs)) (T (x :: ys)) | Yes Refl | No p = No $ p . overT . snd . vectInjective . underT
            decEq (T (x :: xs)) (T (x :: xs)) | Yes Refl | Yes Refl = Yes Refl
    decEq (V _) (T _) = No vNotEqT
    decEq (T _) (V _) = No (negEqSym vNotEqT)
    decEq (T (x :: xs)) (T []) = No $ consNotEqNil . underT
    decEq (T []) (T (x :: xs)) = No $ negEqSym (consNotEqNil . underT)


typToNat : Typ -> Nat
typToNat TInt = 0
typToNat TBool = 1

natToTyp : Nat -> Typ
natToTyp 0 = TInt
natToTyp 1 = TBool
natToTyp _ = TInt

typToNatToTypId : (t : Typ) -> t = natToTyp (typToNat t)
typToNatToTypId TInt = Refl
typToNatToTypId TBool = Refl

typToNatInj : {a, b : Typ} -> typToNat a = typToNat b -> a = b
typToNatInj p = rewrite typToNatToTypId a in rewrite typToNatToTypId b in cong natToTyp p

DecEq Typ where
    decEq x y with (decEq (typToNat x) (typToNat y))
        _ | Yes p = Yes $ typToNatInj p
        _ | No p = No $ p . cong typToNat


DecEq Dir where
    decEq Left Left = Yes Refl
    decEq Right Right = Yes Refl
    decEq Left Right = No p where
        p : Equal {a=Dir, b=Dir} Left Right -> Void
        p Refl impossible
    decEq Right Left = No p where
        p : Equal {a=Dir, b=Dir} Right Left -> Void
        p Refl impossible


mutual
    id0 : Block0
    id0 = MkBlock0 "id" up where
        up : (y : Shp') -> Maybe (Block1 y)
        up (x1, x2) with (decEq x1 x2)
            up (x, x)   | Yes Refl = Just id1
            up (x1, x2) | No _ = Nothing
    
    id1 : Block1 (x, x)
    id1 = MkBlock1 id0 up where
        up : (y : DShp') -> Maybe (Block2 y)
        up (x1, x2) with (decEq x1 x2)
            up (x, x)   | Yes Refl = Just id2
            up (x1, x2) | No _ = Nothing

    id2 : Block2 (x, x)
    id2 = MkBlock2 id1 (\(x, y) => (y, x))
