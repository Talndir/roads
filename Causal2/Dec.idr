module Causal2.Dec

import public Decidable.Equality
import public Decidable.Decidable
import public Data.Fun
import public Data.Rel
import Causal2.Data
import Causal2.Utils

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

export
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
typToNat TUnit = 2

natToTyp : Nat -> Typ
natToTyp 0 = TInt
natToTyp 1 = TBool
natToTyp 2 = TUnit
natToTyp _ = TInt

typToNatToTypId : (t : Typ) -> t = natToTyp (typToNat t)
typToNatToTypId TInt = Refl
typToNatToTypId TBool = Refl
typToNatToTypId TUnit = Refl

typToNatInj : {a, b : Typ} -> typToNat a = typToNat b -> a = b
typToNatInj p = rewrite typToNatToTypId a in rewrite typToNatToTypId b in cong natToTyp p

export
DecEq Typ where
    decEq x y with (decEq (typToNat x) (typToNat y))
        _ | Yes p = Yes $ typToNatInj p
        _ | No p = No $ p . cong typToNat

export
DecEq Dir where
    decEq Left Left = Yes Refl
    decEq Right Right = Yes Refl
    decEq Left Right = No p where
        p : Equal {a=Dir, b=Dir} Left Right -> Void
        p Refl impossible
    decEq Right Left = No p where
        p : Equal {a=Dir, b=Dir} Right Left -> Void
        p Refl impossible

[DecLeft] Decidable 1 [DShp] Lefts where
    decide (V (_, Left)) = Yes VLefts
    decide (V (_, Right)) = No p where
        p : Lefts (V (_, Right)) -> Void
        p VLefts impossible
    decide (T []) = Yes (TLefts VLefts')
    decide (T (x :: xs)) with (decide @{DecLeft} x)
        _ | No p = No $ \(TLefts (TLefts' l ls)) => p l
        _ | Yes p with (assert_total $ decide @{DecLeft} (T xs))
            _ | No q = No $ \(TLefts (TLefts' l ls)) => q (TLefts ls)
            _ | Yes (TLefts q) = Yes (TLefts (TLefts' p q))

export
decLeft : (x : DShp) -> Dec (Lefts x)
decLeft = decide @{DecLeft}

[DecRight] Decidable 1 [DShp] Rights where
    decide (V (_, Right)) = Yes VRights
    decide (V (_, Left)) = No p where
        p : Rights (V (_, Left)) -> Void
        p VRights impossible
    decide (T []) = Yes (TRights VRights')
    decide (T (x :: xs)) with (decide @{DecRight} x)
        _ | No p = No $ \(TRights (TRights' l ls)) => p l
        _ | Yes p with (assert_total $ decide @{DecRight} (T xs))
            _ | No q = No $ \(TRights (TRights' l ls)) => q (TRights ls)
            _ | Yes (TRights q) = Yes (TRights (TRights' p q))

export
decRight : (x : DShp) -> Dec (Rights x)
decRight = decide @{DecRight}

oppSameType : (t : Typ) -> (u : Typ) -> {d : Dir} -> Opp (V (t, d)) (V (u, swp d)) -> t = u
oppSameType t u v {d} with (v)
    oppSameType t t v {d=Left} | VOppLR = Refl
    oppSameType t t v {d=Right} | VOppRL = Refl

oppSameDirImposs : Opp (V (_, d)) (V (_, d)) -> Void
oppSameDirImposs VOppLR impossible

oppVTImposs : Opp (V _) (T _) -> Void
oppVTImposs VOppLR impossible

oppTEImposs : Opp (T (x :: xs)) (T []) -> Void
oppTEImposs VOppLR impossible

[DecOpp] Decidable 2 [DShp, DShp] Opp where
    decide (V (t, Left)) (V (u, Right)) with (decEq t u)
        decide (V (t, Left)) (V (t, Right)) | Yes Refl = Yes VOppLR
        _ | No p = No $ p . oppSameType t u
    decide (V (t, Right)) (V (u, Left)) with (decEq t u)
        decide (V (t, Right)) (V (t, Left)) | Yes Refl = Yes VOppRL
        _ | No p = No $ p . oppSameType t u
    decide (V (t, Left)) (V (u, Left)) = No oppSameDirImposs
    decide (V (t, Right)) (V (u, Right)) = No oppSameDirImposs
    decide (V x) (T xs) = No oppVTImposs
    decide (T xs) (V x) = No $ oppVTImposs . oppOpp
    decide (T []) (T []) = Yes (TOpp VOpp')
    decide (T (x :: xs)) (T []) = No oppTEImposs
    decide (T []) (T (x :: xs)) = No $ oppTEImposs . oppOpp
    decide (T (x :: xs)) (T (y :: ys)) with (decide @{DecOpp} x y)
        _ | No p = No $ \(TOpp (TOpp' t ts)) => p t
        _ | Yes p with (assert_total $ decide @{DecOpp} (T xs) (T ys))
            _ | No q = No $ \(TOpp (TOpp' t ts)) => q (TOpp ts)
            _ | Yes (TOpp q) = Yes (TOpp (TOpp' p q))

export
decOpp : (x : DShp) -> (y : DShp) -> Dec (Opp x y)
decOpp = decide @{DecOpp}
