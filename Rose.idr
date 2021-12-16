module Rose

import public DVect

public export
data Rose a = V a | T (Vect n (Rose a))

--public export
Show a => Show (Rose a) where
    show (V x) = show x
    show (T rs) = show rs

public export
Functor Rose where
    map f (V x) = V (f x)
    map f (T rs) = T (map (map f) rs)

public export
nil : Functor f => f a -> f Unit
nil = map (const ())

public export
spf : {f : Type -> Type} -> Functor f => f a -> f b -> Type
spf x y = nil x = nil y

public export
shape : {f : Type -> Type} -> Functor f => {a : Type} -> f a -> Type -> Type
shape x b = (y : f b ** nil x = nil y)

public export
shape2 : {f : Type -> Type} -> Functor f => {a : Type} -> (f a, f a) -> Type -> Type
shape2 (x, y) b = (z : (f b, f b) ** (nil (fst z) = nil x, nil (snd z) = nil y))

public export
makeShape : {f : Type -> Type} -> Functor f => {a : Type} -> (x : f a) -> shape x a
makeShape x = (x ** Refl)

mapLenP : (f : a -> b) -> (xs : Vect n a) -> (n = length (map f xs))
mapLenP f [] = Refl
mapLenP f (x :: xs) = cong S (mapLenP f xs)

nilP : {xs : Vect n (Rose a)} -> {ys : Vect m (Rose b)} -> (pf : nil (T xs) = nil (T ys)) -> n = m
nilP {xs} {ys} pf = rewrite sym (lengthCorrect (map nil xs)) in rewrite sym (lengthCorrect (map nil ys)) in cong len pf where
    len : Rose _ -> Nat
    len (V _) = 0
    len (T rs) = length rs

public export
extractT : (xs : Vect n (Rose a)) -> (v : shape (T xs) b) -> (ys : Vect n (Rose b) ** T ys = fst v)
extractT xs (T rs ** pf) = (rewrite nilP pf in rs ** rewrite nilP pf in Refl)

makeFunc : Type -> Type -> Type
makeFunc a t = t -> a

public export 
Dv : {a : Type} -> Vect n (Rose a) -> Type -> Type
Dv xs b = DVect {b=Rose b} spf xs

propagateP : (xs : Vect n (Rose a)) -> (ys : Vect n (Rose b)) -> (pf : map Rose.nil xs = map Rose.nil ys) -> (vs : Dv xs b ** ys = extract vs)
propagateP [] [] _ = ([] ** Refl)
propagateP (x :: xs) (y :: ys) pf =
    let (h, t) = vectInjective pf in
    let (vs ** ps) = propagateP xs ys t in
    ((y ** h) :: vs ** cong (y::) ps)

underT : {xs : Vect n (Rose a)} -> {ys : Vect m (Rose b)} -> (pf : T xs = T ys) -> xs = ys
underT Refl = Refl

rwrVect : (eq : n = m) -> {xs : Vect n a} -> {ys : Vect m b} -> Equal {a = Vect n a} {b = Vect m b} xs ys -> Equal {a = Vect n a} {b = Vect n b} xs (rewrite eq in ys)
rwrVect Refl Refl = Refl

public export
extractT'' : (xs : Vect m (Rose a)) -> (v : shape (T xs) b) -> (ys : Dv xs b ** fst v = T (extract ys))
extractT'' xs (T rs ** pf) = let p' = nilP pf in let (vs ** p) = propagateP xs (rewrite p' in rs) (rwrVect p' (underT pf)) in (vs ** rewrite (sym p') in cong T p)

makeT' : (xs : Vect n (Rose a)) -> (vs : Dv xs b) -> (ys : (y : Vect n (Rose b) ** map Rose.nil y = map Rose.nil xs) ** fst ys = extract vs)
makeT' (x :: xs) (y :: ys) = let ((vs ** ps) ** qs) = makeT' xs ys in let (v ** p) = y in ((v :: vs ** rewrite ps in rewrite p in Refl) ** rewrite qs in Refl)
makeT' [] [] = (([] ** Refl) ** Refl)

public export
makeT : {xs : Vect n (Rose a)} -> (vs : Dv xs b) -> (ys : shape (T xs) b ** fst ys = T (extract vs))
makeT {xs} vs = let ((v ** p) ** q) = makeT' xs vs in ((T v ** rewrite p in Refl) ** cong T q)

public export
unshape : {f : Type -> Type} -> Functor f => {x : f a} -> shape {f=f} x b -> f b
unshape (x ** _) = x
