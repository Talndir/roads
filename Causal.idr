module Causal

import Data.Vect
import Data.Vect.Properties.Map
import Indexed
import IAE
import Data.HVect
import Data.Nat
import Debug.Trace

data Rose a = V a | T (Vect n (Rose a))

Show a => Show (Rose a) where
    show (V x) = show x
    show (T rs) = show rs

Functor Rose where
    map f (V x) = V (f x)
    map f (T rs) = T (map (map f) rs)

data Dir = In | Out

Eq Dir where
    In == In = True
    Out == Out = True
    _ == _ = False

swap : Dir -> Dir
swap In = Out
swap Out = In

{-
--Hetero : (f : Type -> Type) -> Functor f => f Type -> Type
--Hetero f ts = (x : f (a : Type ** a) ** map fst x = ts)

Shaped : (f : Type -> Type) -> Functor f => (a : Type) -> f Unit -> Type
Shaped f a ts = (x : f (v : Unit ** a) ** map fst x = ts)

Shape : Type
Shape = Rose Unit

--Tuple : Rose Type -> Type
--Tuple = Hetero Rose

--Typ : (Rose Type, Rose Type) -> Type
--Typ (ts, us) = (Hetero Rose ts, Hetero Rose us)

Tuple : Type -> Shape -> Type
Tuple = Shaped Rose

Typ : Type -> (Shape, Shape) -> Type
Typ a (ts, us) = (Tuple a ts, Tuple a us)

Iso : Type -> (Shape, Shape) -> Type
Iso a ts = Typ a ts -> Typ a ts

conv : (ts, us : Shape) -> Iso a (ts, us) -> Typ Dir (ps, qs)
conv ts us iso = ?w
-}

nil : Functor f => f a -> f Unit
nil = map (const ())

Shape : {f : Type -> Type} -> Functor f => f Unit -> Type -> Type
Shape x a = (y : f a ** nil y = x)

(Functor f, Show a, Show (f a)) => Show (Shape {f=f} s a) where
    show (y ** p) = show y

Shape2 : {f : Type -> Type} -> Functor f => (f Unit, f Unit) -> Type -> Type
Shape2 (x, y) a = (z : (f a, f a) ** (nil (fst z) = x, nil (snd z) = y))

makeShape : {f : Type -> Type} -> Functor f => {a : Type} -> (x : f a) -> Shape (nil x) a
makeShape x = (x ** Refl)

---mapFusion : (f : b -> c) -> (g : a -> b) -> (rs : List a) -> map f (map g rs) = map (f . g) rs
---mapFusion f g [] = Refl
---mapFusion f g (x :: xs) = rewrite mapFusion f g xs in Refl

---mapExtensional : (f : a -> b) -> (g : a -> b) -> ((x : a) -> f x = g x) -> (rs : List a) -> map f rs = map g rs
---mapExtensional f g pf [] = Refl
---mapExtensional f g pf (x :: xs) = rewrite mapExtensional f g pf xs in rewrite pf x in Refl

mapFuseRose : (f : b -> c) -> (g : a -> b) -> (rs : Rose a) -> map f (map g rs) = map (f . g) rs
mapFuseRose f g (V x) = Refl
mapFuseRose f g (T xs) =
    rewrite mapFusion (map f) (map g) xs in cong T
    (rewrite mapExtensional (map f . map g) (map (f . g)) (mapFuseRose f g) xs in Refl)

Shp : Type
Shp = Rose Unit

Shp' : Type
Shp' = (Shp, Shp)

mapId : (rs : List a) -> map Prelude.Basics.id rs = rs
mapId [] = Refl
mapId (x :: xs) = rewrite mapId xs in Refl

makeShape' : (s : Shp) -> {a : Type} -> a -> Shape s a
makeShape' s x = (map (const x) s ** rewrite pf1 s in rewrite pf2 s in Refl) where
    pf1 : (s : Shp) -> nil (map (const x) s) = nil s
    pf1 = mapFuseRose (const ()) (const x)
    pf2 : (s : Shp) -> nil s = s
    pf2 (V ()) = Refl
    pf2 (T xs) = cong T (rewrite mapExtensional nil id pf2 xs in mapId xs)

Tuple : Shp -> Type -> Type
Tuple = Shape {f=Rose}

Typ : Shp' -> Type -> Type
Typ (ts, us) a = (Tuple ts a, Tuple us a)

data Iso : Shp' -> Shp' -> Type where
    Is : (forall a . Typ ts a -> Typ us a) -> (forall a . Typ us a -> Typ ts a) -> Iso ts us

conv : {ts, us : Shp'} -> Iso ts us -> Typ ts Dir
conv {us=(ins, outs)} (Is _ g) = g (makeShape' ins In, makeShape' outs Out)

DShp : Type
DShp = Rose Dir

DShp' : Type
DShp' = (DShp, DShp)

nuke : Typ (ts, us) Dir -> DShp'
nuke ((x ** _), (y ** _)) = (x, y)

data Impl : Type -> DShp' -> Type where
    Imp : (Tuple ins a -> Tuple outs a) -> (iso : Iso (dom, cod) (ins, outs)) -> Impl a (nuke $ conv iso)

--eval : Impl (dom, cod) (ins, outs) -> 

compl : DShp -> DShp
compl = map swap

data RComb : (k : DShp' -> Type) -> DShp' -> Type where
    Seq : k (a, b) -> k (compl b, c) -> RComb k (a, c)
    Par : k (a, b) -> k (c, d) -> RComb k (T [a, c], T [b, d])
    Inv : k (a, b) -> RComb k (b, a)

IFunctor RComb where
    imap f (Seq q r) = Seq (f q) (f r)
    imap f (Par q r) = Par (f q) (f r)
    imap f (Inv q) = Inv (f q)

--

--g : Tuple (T [V (), T [V (), V ()]]) Nat -> Nat
--g (T [V x, T [V y, V z]] ** Refl) = x + y + z

underT : {xs : Vect n (Rose a)} -> {ys : Vect m (Rose b)} -> (pf : T xs = T ys) -> xs = ys
underT Refl = Refl

underT' : {x : Rose a} -> {y : Rose b} -> (pf : T (x :: xs) = T (y :: ys)) -> x = y
underT' Refl = Refl

underT'' : {x : Rose a} -> {y : Rose a} -> (pf : T (x :: xs) = T (y :: ys)) -> (x = y, T xs = T ys)
underT'' Refl = (Refl, Refl)

overT : x = y -> T [x] = T [y]
overT Refl = Refl

addEq : {x, y : a} -> {xs, ys : Vect n a} -> x = y -> xs = ys -> (x :: xs) = (y :: ys)
addEq Refl Refl = Refl

mapT : {x : Rose a} -> {xs : Vect n (Rose b)} -> map f x = T xs -> (ys : Vect n (Rose a) ** x = T ys)
mapT {x=T ys} Refl = (ys ** Refl)

repl1 : (is : Vect n Shp) -> (u : Rose a) -> Type
repl1 is u = nil u = T is

{-
build : {p, q, ip, op, iq, oq : Shp} -> (Ayy p (ip, op), Ayy q (iq, oq)) -> (forall b . Tuple (T [p, q]) b -> Typ (T [ip, iq], T [op, oq]) b)
build {ip, iq, op, oq} (Ay fp _, Ay fq _) (T [x, y] ** pf@Refl) =
    let (h, t) = extrVectPf (underT pf) in
    let ((xi ** xipf), (xo ** xopf)) = fp (x ** h) in
    let ((yi ** yipf), (yo ** yopf)) = fq (y ** t) in
    let px = cong T (vectProof xipf yipf) in
    let py = cong T (vectProof xopf yopf) in
    ((T [xi, yi] ** px), (T [xo, yo] ** py))
build _ _ = ?kk

build' : {p, q, ip, op, iq, oq : Shp} -> (Ayy p (ip, op), Ayy q (iq, oq)) -> (forall b . Typ (T [ip, iq], T [op, oq]) b -> Tuple (T [p, q]) b)
build' {p, q, ip, iq, op, oq} (Ay _ gp, Ay _ gq) ((T [xi, yi] ** pfi), (T [xo, yo] ** pfo)) =
    let (hi, ti) = extrVectPf (underT pfi) in
    let (ho, to) = extrVectPf (underT pfo) in
    let (x ** px) = gp ((xi ** hi), (xo ** ho)) in
    let (y ** py) = gq ((yi ** ti), (yo ** to)) in
    (T [x, y] ** cong T (vectProof px py))
build' _ _ = ?jj

mkiso : (ds : DShp) -> (us : Shp' ** Ayy (nil ds) us)
mkiso (T [a, b]) =
    let (((sai, sao) ** isoa), ((sbi, sbo) ** isob)) = (mkiso a, mkiso b) in
    let f = build (isoa, isob) in
    let g = build' (isoa, isob) in
    ((T [sai, sbi], T [sao, sbo]) ** (Ay f g))
mkiso _ = ?mk
-}

{-
data Ayy : Shp -> Shp' -> Type where
    Ay : (f : forall b . Tuple ts b -> Typ us b)
      -> (g : forall b . Typ us b -> Tuple ts b)
      -> Ayy ts us

Shaped : {f : Type -> Type} -> Functor f => f Unit -> Type -> Type
Shaped {f} x a = (y : f (z : Unit ** a) ** map fst y = x)

vectProof : {a, b : Type} -> {x, y : a} -> {p, q : b} -> (x = p) -> (y = q) -> Equal {a=Vect 2 a} {b=Vect 2 b} [x, y] [p, q]
vectProof Refl Refl = Refl

extrVectPf : Equal {a=Vect 2 a} {b=Vect 2 b} [x, y] [p, q] -> (x = p, y = q)
extrVectPf pf = let (h, t) = vectInjective pf in let (t', _) = vectInjective t in (h, t')

mkAyy : Vect n Shp -> Vect n Shp -> Vect n Shp -> Vect n Type
mkAyy = zipWith3 (\x, y, z => Ayy x (y, z))

mkPfs : Vect n a -> Vect n a -> Vect n Type
mkPfs = zipWith (\x, y => x = y)

extrVectPfs : {xs, ys : Vect n a} -> xs = ys -> HVect (mkPfs xs ys)
extrVectPfs {xs=(x::xss)} {ys=(y::yss)} pf = let (h, t) = vectInjective pf in h :: extrVectPfs t
extrVectPfs {xs=[]} {ys=[]} _ = []

mkFun : Vect n Type -> Vect n Type -> Vect n Type
mkFun = zipWith (\x, y => x -> y)

hmap : {xs, ys : Vect n Type} -> HVect (mkFun xs ys) -> HVect xs -> HVect ys
hmap {xs=x::xss, ys=y::yss} (f :: fs) (v :: vs) = f v :: hmap fs vs
hmap {xs=[], ys=[]} [] [] = []

mapVect : {xs : Vect n a} -> {ys : Vect m b} -> map f xs = ys -> n = m
mapVect Refl = Refl

rwrVect : (eq : n = m) -> {xs : Vect n a} -> {ys : Vect m b} -> Equal {a = Vect n a} {b = Vect m b} xs ys -> Equal {a = Vect n a} {b = Vect n b} xs (rewrite eq in ys)
rwrVect Refl Refl = Refl

buildV : {ts, is, os : Vect (S m) Shp} -> HVect (mkAyy ts is os) -> (forall b . Tuple (T ts) b -> Typ (T is, T os) b)
buildV {is=[i], os=[o]} [Ay f _] (T [x] ** pf@Refl) =
    let ((xi ** xipf), (xo ** xopf)) = f (x ** underT' pf) in
    ((T [xi] ** overT xipf), (T [xo] ** overT xopf))
buildV {is=(i :: i' :: is), os=(o :: o' :: os)} ((Ay f _) :: iso :: isos) (T (x :: x' :: xs) ** pf@Refl) =
    let (p, ps) = vectInjective (underT pf) in
    let ((xi ** xipf), (xo ** xopf)) = f (x ** p) in
    let ((u ** pu), (v ** pv)) = buildV (iso :: isos) (T (x' :: xs) ** cong T ps) in
    let ((u' ** pu'), (v' ** pv')) = (mapT pu, mapT pv) in
    let pu'' = addEq xipf . underT $ replace {p=repl1 (i' :: is)} pu' pu in
    let pv'' = addEq xopf . underT $ replace {p=repl1 (o' :: os)} pv' pv in
    ((T (xi :: u') ** cong T pu''), (T (xo :: v') ** cong T pv''))

buildV' : {ts, is, os : Vect (S m) Shp} -> HVect (mkAyy ts is os) -> (forall b . Typ (T is, T os) b -> Tuple (T ts) b)
buildV' {ts=[t]} [Ay _ g] ((T [i] ** pfi@Refl), (T [o] ** pfo@Refl)) =
    let (x ** px) = g ((i ** underT' pfi), (o ** underT' pfo)) in
    (T [x] ** overT px)
buildV' {ts=(t :: t' :: ts)} ((Ay _ g) :: iso :: isos) ((T (i :: i' :: is) ** pfi@Refl), (T (o :: o' :: os) ** pfo@Refl)) =
    let (hi, ti) = vectInjective (underT pfi) in
    let (ho, to) = vectInjective (underT pfo) in
    let (x ** px) = g ((i ** hi), (o ** ho)) in
    let (ys ** py) = buildV' (iso :: isos) ((T (i' :: is) ** cong T ti), (T (o' :: os) ** cong T to)) in
    let (ys' ** py') = mapT py in
    (T (x :: ys') ** cong T . addEq px . underT $ replace {p=repl1 (t' :: ts)} py' py)

buildVV : {ts, is, os : Vect (S m) Shp} -> HVect (mkAyy ts is os) -> Ayy (T ts) (T is, T os)
buildVV x = Ay (buildV x) (buildV' x)

hetmap : {a : Type} -> {p : a -> Type} -> (f : (x : a) -> p x) -> (xs : Vect n a) -> HVect (map p xs)
hetmap f (x :: xs) = f x :: hetmap f xs
hetmap f [] = []

hetmap' : (f : (ds : DShp) -> (us : Shp' ** Ayy (nil ds) us)) -> (xs : Vect n DShp) -> (is : Vect n Shp ** (os : Vect n Shp ** HVect (mkAyy (map nil xs) is os)))
hetmap' f (x :: xs) =
    let ((i, o) ** y) = f x in
    let (is ** (os ** ys)) = hetmap' f xs in
    (i :: is ** (o :: os ** y :: ys))
hetmap' _ [] = ([] ** ([] ** []))

mkiso' : (ds : DShp) -> (us : Shp' ** Ayy (nil ds) us)
mkiso' (T (x :: xs)) =
    let (is ** (os ** ys)) = hetmap' mkiso' (x :: xs) in
    let w = buildVV ys in
    ((T is, T os) ** w)
mkiso' (V In) = ((T [V ()], T []) ** Ay f g) where
    f : Tuple (V ()) b -> Typ (T [V ()], T []) b
    f (v ** p) = ((T [v] ** cong (T . (::[])) p), (T [] ** Refl))
    g : Typ (T [V ()], T []) b -> Tuple (V ()) b
    g v = let ((T [x] ** px), (T [] ** py)) = v in (x ** underT' px)
mkiso' (V Out) = ((T [], T [V ()]) ** Ay f g) where
    f : Tuple (V ()) b -> Typ (T [], T [V ()]) b
    f (v ** p) = ((T [] ** Refl), (T [v] ** cong (T . (::[])) p))
    g : Typ (T [], T [V ()]) b -> Tuple (V ()) b
    g v = let ((T [] ** px), (T [y] ** py)) = v in (y ** underT' py)
mkiso' (T []) = ((T [], T []) ** Ay f g) where
    f : Tuple (T []) b -> Typ (T [], T []) b
    f (v ** p) = ((T [] ** Refl), (T [] ** Refl))
    g : Typ (T [], T []) b -> Tuple (T []) b
    g x = (T [] ** Refl)

itest : (us : Shp ** Tuple us Int)
itest =
    let (us ** Ay f g) = mkiso' (fst x) in
    (T [V (), T [V (), V ()]] ** g (f y)) where
    x : Tuple (T [V (), T [V (), V ()]]) Dir
    x = (T [V In, T [V Out, V In]] ** Refl)
    y : Tuple (T [V (), T [V (), V ()]]) Int
    y = (T [V 1, T [V 2, V 3]] ** Refl)
-}

data Isso : Shp -> Nat -> Nat -> Type where
    Iss : (f : forall b . Tuple ts b -> (Vect n b, Vect m b))
      -> (g : forall b . (Vect n b, Vect m b) -> Tuple ts b)
      -> Isso ts n m
{-
mkIsso : Vect n Shp -> Vect n Nat -> Vect n Nat -> Vect n Type
mkIsso = zipWith3 Isso

sumpf : (n, m : Nat) -> (ms : Vect k Nat) -> n + (foldl (+) m ms) = foldl (+) (n + m) ms
sumpf n m (v :: vs) = rewrite sumpf n (m + v) vs in cong (\e => foldl (+) e vs) (plusAssociative n m v)
sumpf n m [] = Refl

sumpf' : (m : Nat) -> (ms : Vect k Nat) -> m + (foldl (+) 0 ms) = foldl (+) m ms
sumpf' m ms = rewrite sumpf m 0 ms in cong (\e => foldl (+) e ms) (plusZeroRightNeutral m)

addone : {n, m : Nat} -> {ns : Vect k Nat} -> Vect n b -> Vect (foldl (+) m ns) b -> Vect (foldl (+) (n+m) ns) b
addone {n, m, ns} v vs = rewrite sym (sumpf n m ns) in v ++ vs

addone' : {n : Nat} -> {ns : Vect k Nat} -> Vect n b -> Vect (sum ns) b -> Vect (foldl (+) n ns) b
addone' {n, ns} v vs = rewrite sym (sumpf' n ns) in v ++ vs

split : {n, m : Nat} -> {ms : Vect k Nat} -> Vect (foldl (+) (n + m) ms) b -> (Vect n b, Vect (foldl (+) m ms) b)
split {n, m, ms} x = splitAt n (rewrite sumpf n m ms in x)

buildT : {ns, ms : Vect (S k) Nat} -> HVect (mkIsso ts ns ms) -> (forall b . Tuple (T ts) b -> (Vect (sum ns) b, Vect (sum ms) b))
buildT {ns=[n], ms=[m]} [Iss f _] (T [x] ** pf@Refl) = f (x ** underT' pf)
buildT {ns=(n::n'::ns), ms=(m::m'::ms)} ((Iss f _) :: iso :: isos) (T (x :: x' :: xs) ** pf@Refl) =
    let (p, ps) = vectInjective (underT pf) in
    let (i, o) = f (x ** p) in
    let (is, os) = buildT {ns=n'::ns, ms=m'::ms} (iso :: isos) (T (x' :: xs) ** cong T ps) in
    (addone i is, addone o os)

buildT' : {ts : Vect (S k) Shp} -> {ns, ms : Vect (S k) Nat} -> HVect (mkIsso ts ns ms) -> (forall b . (Vect (sum ns) b, Vect (sum ms) b) -> Tuple (T ts) b)
buildT' {ts=[t], ns=[n], ms=[m]} [Iss _ g] (is, os) = let (x ** pf) = g (is, os) in (T [x] ** overT pf)
buildT' {ts=(t :: t' :: ts), ns=(n::n'::ns), ms=(m::m'::ms)} ((Iss _ g) :: iso :: isos) (is, os) =
    let ((i, is'), (o, os')) = (split is, split os) in
    let (x ** pf) = g (i, o) in
    let (xs ** pfs) = buildT' {ts=t'::ts, ns=n'::ns, ms=m'::ms} (iso::isos) (is', os') in
    let (xs' ** pfs') = mapT pfs in
    (T (x :: xs') ** cong T . addEq pf . underT $ replace {p=repl1 (t' :: ts)} pfs' pfs)

buildTT : {ts : Vect (S k) Shp} -> {ns, ms : Vect (S k) Nat} -> HVect (mkIsso ts ns ms) -> Isso (T ts) (sum ns) (sum ms)
buildTT x = Iss (buildT x) (buildT' x)

hetmap2 : (f : (ds : DShp) -> (n : Nat ** (m : Nat ** Isso (nil ds) n m))) -> (xs : Vect n DShp) -> (ns : Vect n Nat ** (ms : Vect n Nat ** HVect (mkIsso (map Causal.nil xs) ns ms)))
hetmap2 f (x :: xs) =
    let (n ** (m **  y)) = f x in
    let (ns ** (ms ** ys)) = hetmap2 f xs in
    (n :: ns ** (m :: ms ** y :: ys))
hetmap2 _ [] = ([] ** ([] ** []))

mkIsso2 : DShp -> Type
mkIsso2 x = (n : Nat ** (m : Nat ** Isso (nil x) n m))

hetmap : {a : Type}
      -> {t : a -> Type}
      -> (f : (x : a) -> t x)
      -> (xs : Vect n a)
      -> HVect (map t xs)
hetmap f (x :: xs) = f x :: hetmap f xs
hetmap _ [] = []

convIsso : {xs : Vect n DShp}
        -> HVect (map Causal.mkIsso2 xs)
        -> (ns : Vect n Nat ** (ms : Vect n Nat ** HVect (mkIsso (map Causal.nil xs) ns ms)))
convIsso {xs=(x::xs)} ((n ** (m ** iso)) :: hs) = let (ns ** (ms ** isos)) = convIsso hs in (n :: ns ** (m :: ms ** iso :: isos))
convIsso {xs=[]} [] = ([] ** ([] ** []))

make : (ds : DShp) -> (n : Nat ** (m : Nat ** Isso (nil ds) n m))
make (T (x :: xs)) =
    let hs = hetmap make (x :: xs) in 
    let (ns ** (ms ** ys)) = convIsso {xs=(x::xs)} hs in
    (sum ns ** (sum ms ** buildTT ys))
make (V In) = (1 ** (0 ** Iss (\(V x ** _) => ([x], [])) (\([x], _) => (V x ** Refl))))
make (V Out) = (0 ** (1 ** Iss (\(V x ** _) => ([], [x])) (\(_, [x]) => (V x ** Refl))))
make (T []) = (0 ** (0 ** Iss (\(_ ** _) => ([], [])) (\(_, _) => (T [] ** Refl))))
-}

rwrVect' : (eq : n = m) -> {xs : Vect n a} -> {ys : Vect m b} -> Equal {a = Vect n a} {b = Vect m b} xs ys -> Equal {a = Vect m a} {b = Vect m b} (rewrite sym eq in xs) ys
rwrVect' Refl Refl = Refl

addToVect : {xs : Vect n (Rose a)} -> {ys : Vect m (Rose b)}
         -> {x : Rose a} -> {y : Rose b}
         -> Equal {a = Rose a} {b = Rose b} x y
         -> Equal {a = Rose a} {b = Rose b} (T xs) (T ys)
         -> Equal {a = Rose a} {b = Rose b} (T (x :: xs)) (T (y :: ys))
addToVect Refl Refl = Refl

make : (ds : DShp) -> (w : (Nat, Nat) ** Isso (nil ds) (fst w) (snd w))
make (T (x :: xs)) =
    let ((n, m) ** (Iss f g)) = make x in
    let ((ns, ms) ** (Iss fs gs)) = make (T xs) in
    ((n + ns, m + ms) ** Iss (
        \(T (u :: us) ** pf) => 
            let (p, ps) = underT'' pf in
            let (a, b) = f (u ** p) in
            let (as, bs) = fs (T us ** ps) in
            (a ++ as, b ++ bs)
    ) (
        \(ps, qs) =>
            let (a, as) = splitAt n ps in
            let (b, bs) = splitAt m qs in
            let (u ** p) = g (a, b) in
            let (T us ** ps) = gs (as, bs) in
            (T (u :: us) ** addToVect p ps)
    ))
make (V In) = ((1, 0) ** Iss (\(V x ** _) => ([x], [])) (\([x], _) => (V x ** Refl)))
make (V Out) = ((0, 1) ** Iss (\(V x ** _) => ([], [x])) (\(_, [x]) => (V x ** Refl)))
make (T []) = ((0, 0) ** Iss (\(_ ** _) => ([], [])) (\(_, _) => (T [] ** Refl)))

-- Expected result: 
--      T [V (), T [V (), V ()]]
--      (2, 1)
--      T [V 1, T [V 2, V 3]]
--      ([1, 3], [2])
--      T [V 1, T [V 2, V 3]]
mtest : (ts : Shp ** (w : (Nat, Nat) ** (Rose Int, (Vect (fst w) Int, Vect (snd w) Int), Rose Int)))
mtest =
    let ((n, m) ** Iss f g) = make (fst x) in
    (T [V (), T [V (), V ()]] ** ((n, m) ** (fst y, f y, fst . g . f $ y))) where
    x : Tuple (T [V (), T [V (), V ()]]) Dir
    x = (T [V In, T [V Out, V In]] ** Refl)
    y : Tuple (T [V (), T [V (), V ()]]) Int
    y = (T [V 1, T [V 2, V 3]] ** Refl)

data Interp : (a : Type) -> (ds : DShp') -> Type where
    Inter : {dl, dr : DShp} -> {nl, nr : (Nat, Nat)}
         -> {auto pfl : nl = fst (make dl)}
         -> {auto pfr : nr = fst (make dr)}
         -> (Vect (fst nl + fst nr) a -> Vect (snd nl + snd nr) a)
         -> Interp a (dl, dr)

Ruby : Type -> DShp' -> Type
Ruby a x = IFree RComb (Interp a) x

infixl 3 <:>
(<:>) : Ruby t (a, b) -> Ruby t (compl b, c) -> Ruby t (a, c)
(q <:> r) = Do (Seq q r)

infixl 3 <|>
(<|>) : Ruby t (a, b) -> Ruby t (c, d) -> Ruby t (T [a, c], T [b, d])
(q <|> r) = Do (Par q r)

inv : Ruby t (a, b) -> Ruby t (b, a)
inv q = Do (Inv q)

add : Interp Int (T [V In, V In], V Out)
add = Inter (\[x, y] => [x + y])

getNums : DShp -> DShp -> ((Nat, Nat), (Nat, Nat))
getNums x y = (fst (make x), fst (make y))

--makePrim : {a : Type} -> {p, q : DShp} -> let ((a,b),(c,d)) = getNums p q in 


sim : Interp a (p, q) -> Typ (nil p, nil q) a -> Typ (nil p, nil q) a
sim (Inter {dl,dr,pfl=pfl@Refl,pfr=pfr@Refl} h) (x, y) with (make dl)
    _ | ((nl1, nl2) ** Iss fl gl) with (make dr)
     _ | ((nr1, nr2) ** (Iss fr gr)) =
        let (li, lo) = fl x in
        let (ri, ro) = fr y in
        let (rl, rr) = splitAt nl2 (h (li ++ ri)) in
        (gl (li, rl), gr (ri, rr))


splitPf : (a, b) = (x, y) -> (a = x, b = y)
splitPf Refl = (Refl, Refl)

pairPf : (a = x, b = y) -> (a, b) = (x, y)
pairPf (Refl, Refl) = Refl

splitPfD : Equal {a=DPair t p} {b=DPair t p} (a ** b) (x ** y) -> (a = x, b = y)
splitPfD Refl = (Refl, Refl)
{-
makepf : {x : DShp} -> {n,m,n',m' : Nat}
      -> {iso : Isso (nil x) n m} -> {iso' : Isso (nil (compl x)) n' m'}
      -> ((n, m) ** iso) = make x -> ((n', m') ** iso') = make (compl x)
      -> (n = m', m = n')
makepf {x=T (x::xs)} pf pf' with (make x) proof mx
    _ | ((a, b) ** (Iss f g)) with (make (T xs)) proof mxs
     _ | ((as, bs) ** (Iss fs gs)) with (splitPfD pf)
      _ | (p1, p2) with (make (compl x)) proof mx'
       _ | ((a', b') ** (Iss f' g')) with (make (compl (T xs))) proof mxs'
        _ | ((as', bs') ** (Iss fs' gs')) with (splitPfD pf')
         _ | (p3, p4) with (makepf (sym mx) (sym mx'))
          _ | (pab, pba) with (makepf (sym mxs) (sym mxs'))
           _ | (pabs, pbas) with (splitPf p1)
            _ | (pn, pm) with (splitPf p3)
             _ | (pn', pm') =
                let pfl = rewrite pm' in rewrite (sym pab) in rewrite (sym pabs) in pn in
                let pfr = rewrite pn' in rewrite (sym pba) in rewrite (sym pbas) in pm
                in (pfl, pfr)
makepf {x=(V In),n=1,m=0,n'=0,m'=1,iso,iso'} pf pf' = (Refl, Refl)
makepf {x=(V Out),n=0,m=1,n'=1,m'=0,iso,iso'} pf pf' = (Refl, Refl)
makepf {x=(T []),n=0,m=0,n'=0,m'=0,iso,iso'} pf pf' = (Refl, Refl)
-}
makepf' : {x : DShp} -> {n,m,n',m' : Nat}
       -> (n, m) = fst (make x) -> (n', m') = fst (make (compl x))
       -> (n = m', m = n')
makepf' {x=T (x::xs)} pf pf' with (make x) proof mx
    _ | ((a, b) ** (Iss f g)) with (make (T xs)) proof mxs
     _ | ((as, bs) ** (Iss fs gs)) with (splitPf pf)
      _ | (pna, pmb) with (make (compl x)) proof mx'
       _ | ((a', b') ** (Iss f' g')) with (make (compl (T xs))) proof mxs'
        _ | ((as', bs') ** (Iss fs' gs')) with (splitPf pf')
         _ | (pna', pmb') with (makepf' (sym (cong fst mx)) (sym (cong fst mx')))
          _ | (pab, pba) with (makepf' (sym (cong fst mxs)) (sym (cong fst mxs')))
           _ | (pabs, pbas) =
            let pfl = rewrite pmb' in rewrite (sym pab) in rewrite (sym pabs) in pna in
            let pfr = rewrite pna' in rewrite (sym pba) in rewrite (sym pbas) in pmb
            in (pfl, pfr)
makepf' {x=V In,n=1,m=0,n'=0,m'=1} pf pf' = (Refl, Refl)
makepf' {x=V Out,n=0,m=1,n'=1,m'=0} pf pf' = (Refl, Refl)
makepf' {x=T [],n=0,m=0,n'=0,m'=0} pf pf' = (Refl, Refl)

makepf2 : {x, y : DShp} -> {nx,mx,ny,my : Nat}
       -> (nx, mx) = fst (make x) -> (ny, my) = fst (make y)
       -> (nx + ny, mx + my) = fst (make (T [x, y]))
makepf2 {x,y} pfx pfy with (make x) proof makex
    _ | ((ax, bx) ** (Iss fx gx)) with (make y) proof makey
     _ | ((ay, by) ** (Iss fy gy)) with (splitPf pfx)
      _ | (nax, mbx) with (splitPf pfy)
       _ | (nay, mby) =
        rewrite nax in rewrite mbx in rewrite nay in rewrite mby in
        rewrite plusZeroRightNeutral ay in rewrite plusZeroRightNeutral by in Refl

idd : {x : DShp} -> Interp a (x, compl x)
idd {x} with (make x) proof mkl
    _ | ((nl, ml) ** isol) with (make (compl x)) proof mkr
        _ | ((nr, mr) ** isor) with (makepf' (sym (cong fst mkl)) (sym (cong fst mkr)))
            _ | (pfl, pfr) =
                let pf1 = cong (fst . fst) mkl in
                let pf2 = cong (fst . fst) mkr in
                let pf3 = cong (snd . fst) mkl in
                let pf4 = cong (snd . fst) mkr in
                Inter (rewrite pf1 in rewrite pf2 in rewrite pf3 in rewrite pf4 in rewrite pfl in rewrite pfr in rewrite plusCommutative mr nr in id)

take' : (n  : Nat) -> Lazy (Vect (n + m) a) -> Lazy (Vect n a)
take' 0 xs = Nil
take' (S k) (x :: xs) = x :: take k xs

drop' : (n : Nat) -> Lazy (Vect (n + m) a) -> Lazy (Vect m a)
drop' 0 xs = xs
drop' (S k) (x :: xs) = drop k xs

tst : Interp a (p, q) -> Interp a (compl q, r) -> Interp a (p, r)
tst (Inter {dl=p,      dr=q,nl=(qnl,qml),nr=(qnr,qmr),pfl=qpfl,pfr=qpfr} qs)
    (Inter {dl=compl q,dr=r,nl=(rnl,rml),nr=(rnr,rmr),pfl=rpfl,pfr=rpfr} rs) =
        Inter {dl=p,   dr=r,nl=(qnl,qml),nr=(rnr,rmr)} ss where
            eq1 : qnr = rml
            eq1 = fst (makepf' qpfr rpfl)
            eq2 : rnl = qmr
            eq2 = sym (snd (makepf' qpfr rpfl))
            rwrml : Vect rml a -> Vect qnr a
            rwrml x = rewrite eq1 in x
            rwqmr : Vect qmr a -> Vect rnl a
            rwqmr x = rewrite eq2 in x
            ss : Vect (qnl + rnr) a -> Vect (qml + rmr) a
            ss vs = tt $ splitAt qnl vs where
                tt : (Vect qnl a, Vect rnr a) -> Vect (qml + rmr) a
                tt (vqnl, vrnr) = vqml ++ vrmr where
                    vqml : Lazy (Vect qml a)
                    vqmr : Lazy (Vect qmr a)
                    vrml : Lazy (Vect rml a)
                    vrmr : Lazy (Vect rmr a)
                    vqml = take' qml (qs (vqnl ++ rwrml vrml))
                    vqmr = drop' qml (qs (vqnl ++ rwrml vrml))
                    vrml = take' rml (rs (rwqmr vqmr ++ vrnr))
                    vrmr = drop' rml (rs (rwqmr vqmr ++ vrnr))

tst' : Interp a (p1, q1) -> Interp a (p2, q2) -> Interp a (T [p1, p2], T [q1, q2])
tst' (Inter {dl=p1,dr=q1,nl=(qnl,qml),nr=(qnr,qmr),pfl=qpfl,pfr=qpfr} qs)
     (Inter {dl=p2,dr=q2,nl=(rnl,rml),nr=(rnr,rmr),pfl=rpfl,pfr=rpfr} rs) =
        Inter {dl=T [p1,p2],dr=T [q1,q2],nl=(qnl+rnl,qml+rml),nr=(qnr+rnr,qmr+rmr),pfl=pfl,pfr=pfr} ss where
            pfl : (qnl + rnl, qml + rml) = fst (make (T [p1, p2]))
            pfl = makepf2 qpfl rpfl
            pfr : (qnr + rnr, qmr + rmr) = fst (make (T [q1, q2]))
            pfr = makepf2 qpfr rpfr
            ss : Vect ((qnl + rnl) + (qnr + rnr)) a -> Vect ((qml + rml) + (qmr + rmr)) a
            ss vs =
                let (t1, t2) = splitAt (qnl + rnl) vs in
                let ((vqnl, vrnl), (vqnr, vrnr)) = (splitAt qnl t1, splitAt qnr t2) in
                let (vqml, vqmr) = splitAt qml (qs (vqnl ++ vqnr)) in
                let (vrml, vrmr) = splitAt rml (rs (vrnl ++ vrnr)) in
                (vqml ++ vrml) ++ (vqmr ++ vrmr)

tst'' : Interp a (p, q) -> Interp a (q, p)
tst'' (Inter {dl=p,dr=q,nl=(nl,ml),nr=(nr,mr),pfl=pfl,pfr=pfr} qs) =
    Inter {dl=q,dr=p,nl=(nr,mr),nr=(nl,ml),pfl=pfr,pfr=pfl} ws where
    ws : Vect (nr + nl) a -> Vect (mr + ml) a
    ws vs =
        let (x, y) = splitAt nr vs in
        let (j, k) = splitAt ml (qs (y ++ x)) in
        k ++ j

alg : RComb (Interp a) x -> Interp a x
alg (Seq q r) = tst q r
alg (Par q r) = tst' q r
alg (Inv q) = tst'' q

handle : {a : Type} -> IFree RComb (Interp a) x -> Interp a x
handle {a} = fold id alg

testing : Interp Int (T [V In, V In], V Out)
testing = tst add idd

id2 : Interp Int (V In, V Out)
id2 = Inter id

simm : Typ (V (), V ()) Int
simm = sim (tst id2 id2) ((V 2 ** Refl), (V 8 ** Refl))

simtst : Typ (T [V (), V ()], V ()) Int
simtst = sim (tst add id2) ((T [V 2, V 4] ** Refl), (V 9 ** Refl))

main : IO ()
main = print . fst . fst $ simm

{-
hzipEq : {a : Type} -> {t : a -> Type} -> (f : (x : a) -> t x)
      -> (xs : Vect n a) -> (ys : HVect (map t xs))
      -> Vect n Type
hzipEq f (x :: xs) (y :: ys) = (f x = y) :: hzipEq f xs ys
hzipEq _ [] [] = []

hzip : {a : Type} -> {t : a -> Type} -> {xs : Vect n a} -> HVect (map t xs)
    -> {b : Type} -> {s : b -> Type} -> {ys : Vect n b} -> HVect (map s ys)
    -> {r : a -> b -> Type}
    -> (f : {x : a} -> t x -> {y : b} -> s y -> r x y)
    -> HVect (zipWith r xs ys)
hzip {xs=(x :: xs),ys=(y :: ys)} (p :: ps) (q :: qs) f = f p q :: hzip ps qs f
hzip {xs=[],ys=[]} [] [] _ = []

hpf : f x :: hetmap f xs = y :: ys -> (f x = y, hetmap f xs = ys)
hpf Refl = (Refl, Refl)

hetmapPf : {a : Type} -> {t : a -> Type} -> {f : (x : a) -> t x}
        -> {xs : Vect n a} -> {ys : HVect (map t xs)}
        -> hetmap f xs = ys
        -> HVect (hzipEq f xs ys)
hetmapPf {xs=(x::xs),ys=(y::ys)} pf = let (p, ps) = hpf pf in p :: hetmapPf ps
hetmapPf {xs=[],ys=[]} Refl = []
-}
{-
mutual
    try : (k : Nat) -> (xs : Vect k DShp) -> (as, bs, as', bs' : Vect k Nat)
       -> {isos : HVect (mkIsso (map Causal.nil xs) as bs)}
       -> {isos' : HVect (mkIsso (map Causal.nil (map Causal.compl xs)) as' bs')}
       -> convIsso {xs=xs} (hetmap Causal.make xs) = (as ** (bs ** isos))
       -> convIsso {xs=map Causal.compl xs} (hetmap Causal.make (map Causal.compl xs)) = (as' ** (bs' ** isos'))
       -> (as = bs', bs = as')
    try (S k) (x::xs) (a::as) (b::bs) (a'::as') (b'::bs') {isos=iso::isos,isos'=iso'::isos'} pf pf' with (make x)
        _ | (ax ** (bx ** isox)) with (hetmap make xs)
            _ | hs with (convIsso hs)
                _ | (asx ** (bsx ** isosx)) with (splitPfD pf)
                    _ | (pf1, pf2) with (vectInjective pf1)
                        _ | (pfa, pfas) with (splitPfD (rewrite sym pfas in pf))
                            _ | (pf3, pf4) = ?tt
    try 0 [] [] [] [] [] Refl Refl = (Refl, Refl)
{-
    try :  (k : Nat) -> (xs : Vect k DShp) -> (as, bs, as', bs' : Vect k Nat)
        -> (hs : HVect (map Causal.mkIsso2 xs)) -> (hs' : HVect (map Causal.mkIsso2 (map Causal.compl xs)))
        -> {isos : HVect (mkIsso (map Causal.nil xs) as bs)}
        -> {isos' : HVect (mkIsso (map Causal.nil (map Causal.compl xs)) as' bs')}
        -> (hetmap Causal.make xs = hs) -> convIsso {xs=xs} hs = (as ** (bs ** isos))
        -> (hetmap Causal.make (map Causal.compl xs) = hs') -> convIsso {xs=map Causal.compl xs} hs' = (as' ** (bs' ** isos'))
        -> (as = bs', bs = as')
        -}
    --try (S k) (_::xs) (a::as) (b::bs) _ _ (h::hs) _ _ pfi _ _ with (convIsso hs) proof pconv
    --    try (S k) (_::xs) (a::as) (b::bs) _ _ ((a ** (b ** iso))::hs) _ _ Refl _ _ | (as ** (bs ** _)) = ?tt--with (splitPfD pfi)
        -- _ | (px1, px2) with (vectInjective px1)
        --  _ | (x1, x2) = ?tt--with (splitPfD px2)
        --  -- _ | (_, _) = ?tt -- in let (p, q) = splitPfD v in ?tt
        --try (S k) (x::xs) (a::as) (b::bs) (a'::as') (b'::bs') (h::hs) (h'::hs') pfh pfi pfh' pfi' | (asx ** (bsx ** _)) = let (w, v) = splitPfD pfi in ?aaa
        --try {k=S v,xs=(x::xs),hs=(n ** (m ** iso))::hs,hs'=h'::hs',as=a::as,bs=b::bs,as'=a'::as',bs'=b'::bs'} pfh pfi pfh' pfi' | (as ** (bs ** _)) with (convIsso hs') proof pconv'
            --try {k=S v,xs=(x::xs),hs=(a ** (b ** iso))::hs,hs'=h'::hs',as=a::as,bs=b::bs,as'=a'::as',bs'=b'::bs'} pfh pfi pfh' pfi' | (as ** (bs ** _)) | (as' ** (bs' ** _)) = --let (p, q) = (splitPfD pfi) in
                --try {k=S v,xs=(x::xs),hs=(a ** (b ** _))::hs,hs'=h'::hs',as=a::as,bs=b::bs,as'=a'::as',bs'=b'::bs'} pfh pfi pfh' pfi' | (as ** (bs ** _)) | (as' ** (bs' ** _)) | (pfa, tmp) = --with (splitPfD pfi')
             -- _ | (pfb, tmp') with (splitPfD tmp)
             --  _ | (pfas, aya) =
                --        let (pfx, pfxs) = hpf pfh in
                --        let (pfx', pfxs') = hpf pfh' in
                --        let (nm, mn) = makepf (sym pfx) (sym pfx') in
                        --let (nms, mns) = try pfxs pconv pfxs' pconv' in
                        --(addEq ?k1 ?k2, ?ll)
                        --?bana--
                        
    --try 0 [] [] [] [] [] [] [] _ _ _ _ = (Refl, Refl)

    makepf : {x : DShp} -> {n,m,n',m' : Nat}
        -> {iso : Isso (nil x) n m} -> {iso' : Isso (nil (compl x)) n' m'}
        -> (n ** (m ** iso)) = make x -> (n' ** (m' ** iso')) = make (compl x)
        -> (n = m', m = n')
    makepf {x=(T (x::xs)),n,m,n',m',iso,iso'} pf pf' with (make x) proof pfx
        _ | (a ** (b ** isox)) with (make (compl x)) proof pfx'
         _ | (a' ** (b' ** isox')) with (hetmap make xs) proof pfs
          _ | hs with (hetmap make (map compl xs)) proof pfs'
           _ | hs' with (convIsso hs)
            _ | (as ** (bs ** isos)) with (convIsso hs')
             _ | (as' ** (bs' ** isos')) with (splitPfD pf)
              _ | (pfn, w) with (splitPfD pf')
               _ | (pfn', w') = let (u, v) = makepf (sym pfx) (sym pfx') in
                    let (pfhs, pfhs') = (hetmapPf pfs, hetmapPf pfs') in
                    --let qq = hzip pfhs pfhs' makepf in
                    ?nan where
        
    makepf {x=(V In),n=1,m=0,n'=0,m'=1,iso,iso'} pf pf' = (Refl, Refl)
    makepf {x=(V Out),n=0,m=1,n'=1,m'=0,iso,iso'} pf pf' = (Refl, Refl)
    makepf {x=(T []),n=0,m=0,n'=0,m'=0,iso,iso'} pf pf' = (Refl, Refl)
-}
