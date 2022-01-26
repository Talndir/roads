module Causal

import Data.Vect
import Data.Vect.Properties.Map
import Indexed
import IAE
import Data.HVect
import Data.Nat

data Rose a = V a | T (Vect n (Rose a))

W : Rose Unit
W = V ()

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

I, O : Rose Dir
I = V In
O = V Out

nil : Functor f => f a -> f Unit
nil = map (const ())

Shape : {f : Type -> Type} -> Functor f => f Unit -> Type -> Type
Shape x a = (y : f a ** nil y = x)

(Functor f, Show a, Show (f a)) => Show (Shape {f=f} s a) where
    show (y ** p) = show y

mapFuseRose : (f : b -> c) -> (g : a -> b) -> (rs : Rose a) -> map f (map g rs) = map (f . g) rs
mapFuseRose f g (V x) = Refl
mapFuseRose f g (T xs) =
    rewrite mapFusion (map f) (map g) xs in cong T
    (rewrite mapExtensional (map f . map g) (map (f . g)) (mapFuseRose f g) xs in Refl)

Shp : Type
Shp = Rose Unit

Shp' : Type
Shp' = (Shp, Shp)

Tuple : Shp -> Type -> Type
Tuple = Shape {f=Rose}

Typ : Shp' -> Type -> Type
Typ (ts, us) a = (Tuple ts a, Tuple us a)

DShp : Type
DShp = Rose Dir

DShp' : Type
DShp' = (DShp, DShp)

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

underT : {xs : Vect n (Rose a)} -> {ys : Vect m (Rose b)} -> (pf : T xs = T ys) -> xs = ys
underT Refl = Refl

underT' : {x : Rose a} -> {y : Rose a} -> (pf : T (x :: xs) = T (y :: ys)) -> (x = y, T xs = T ys)
underT' Refl = (Refl, Refl)

addEq : {x, y : a} -> {xs, ys : Vect n a} -> x = y -> xs = ys -> (x :: xs) = (y :: ys)
addEq Refl Refl = Refl

data Isso : Shp -> Nat -> Nat -> Type where
    Iss : (f : forall b . Tuple ts b -> (Vect n b, Vect m b))
      -> (g : forall b . (Vect n b, Vect m b) -> Tuple ts b)
      -> Isso ts n m

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
            let (p, ps) = underT' pf in
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

replmk : (ns : (Nat, Nat)) -> (x : Rose Dir) -> Type
replmk ns x = ns = fst (make x)

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

-- Expecting (T [V 2, V 4] ** Refl, V 6 ** Refl)
--simtst : Typ (T [V (), V ()], V ()) Int
--simtst = sim (tst add idd) ((T [V 2, V 4] ** Refl), (V 9 ** Refl))

takeOne : Stream a -> (a, Stream a)
takeOne (x :: xs) = (x, xs)

combine : Vect n a -> Vect n (Stream a) -> Vect n (Stream a)
combine (x :: xs) (y :: ys) = (x :: y) :: combine xs ys
combine [] [] = []

liftStr : (Vect n a -> Vect m a) -> Vect n (Stream a) -> Vect m (Stream a)
liftStr f xs = let (hs, ts) = unzip (map takeOne xs) in combine (f hs) (liftStr f ts)

lift : Interp a x -> Interp (Stream a) x
lift (Inter {dl,dr,nl,nr} f) = Inter {dl,dr,nl,nr} (liftStr f)

{-
pfInOut : {x : Rose t} -> (n, m) = fst (make (mkIn x)) -> (m = 0, (0, n) = fst (make (mkOut x)))
pfInOut {x=V x} Refl = (Refl, Refl)
pfInOut {x=T []} Refl = (Refl, Refl)
pfInOut {x=T (x::xs)} pf with (make (mkIn x)) proof mx
    _ | ((a, b) ** (Iss f g)) with (make (mkIn (T xs))) proof mxs
     _ | ((as, bs) ** (Iss fs gs)) with (make (mkOut x)) proof mx'
      _ | ((a', b') ** (Iss f' g')) with (make (mkOut (T xs))) proof mxs'
       _ | ((as', bs') ** (Iss fs' gs')) =
        let (pfx, pfxs) = (cong fst mx, cong fst mxs) in
        let (pfx', pfxs') = (cong fst mx', cong fst mxs') in
        let (Refl, r2) = pfInOut {x=x} (sym pfx) in
        let (Refl, s2) = pfInOut {x=T xs} (sym pfxs) in
        let (Refl, t2) = splitPf pf in
        let (Refl, Refl) = splitPf (trans r2 pfx') in
        let (Refl, Refl) = splitPf (trans s2 pfxs') in
        (t2, Refl)

nilmap : (x : Rose a) -> (f : a -> b) -> nil (map f x) = nil x
nilmap (V x) f = Refl
nilmap (T []) f = Refl
nilmap (T (x :: xs)) f = cong T (addEq (nilmap x f) (underT $ nilmap (T xs) f))

nileq : (x : Rose Unit) -> nil x = x
nileq (V ()) = Refl
nileq (T []) = Refl
nileq (T (x :: xs)) = cong T (addEq (nileq x) (underT $ nileq (T xs)))

delay : {x : Shp} -> Tuple x a -> Ruby (Stream a) (mkIn x, mkOut x)
delay {x} (v ** pv) with (make (mkIn x)) proof pf
    _ | ((n, m) ** (Iss f _)) with (make (mkOut x)) proof pf'
     _ | ((n', m') ** _) =
        let (pfin, pfout) = (cong fst pf, cong fst pf') in
        let (Refl, pfb) = pfInOut (sym pfin) in
        let (Refl, Refl) = splitPf (trans pfb pfout) in
        let pv' = trans pv (sym (trans (nilmap x (const In)) (nileq x))) in
        let (out, _) = f (v ** pv') in
        Ret (Inter (rewrite pfin in rewrite pfout in rewrite plusZeroRightNeutral n in combine out))
-}

-- Primitives

{-
id : {x : DShp} -> Ruby a (x, compl x)
id {x} with (make x) proof mkl
    _ | ((nl, ml) ** isol) with (make (compl x)) proof mkr
        _ | ((nr, mr) ** isor) with (makepf' (sym (cong fst mkl)) (sym (cong fst mkr)))
            _ | (pfl, pfr) =
                let pf1 = cong (fst . fst) mkl in
                let pf2 = cong (fst . fst) mkr in
                let pf3 = cong (snd . fst) mkl in
                let pf4 = cong (snd . fst) mkr in
                Ret $ Inter (rewrite pf1 in rewrite pf2 in rewrite pf3 in rewrite pf4 in
                rewrite pfl in rewrite pfr in rewrite plusCommutative mr nr in id)

outl : {x: DShp} -> {y : Shp} -> Ruby a (T [x, mkIn y], compl x)
outl {x, y} with (make x) proof mkx
    _ | ((nx, mx) ** _) with (make (compl x)) proof mkx'
     _ | ((nx', mx') ** _) with (make (mkIn y)) proof mky
      _ | ((ny, my) ** _) =
        let pfx = sym $ cong fst mkx in
        let pfx' = sym $ cong fst mkx' in
        let pfy = sym $ cong fst mky in
        let z = makepf2 {x=x} {y=mkIn y} pfx pfy in
        let (Refl, Refl) = makepf' pfx pfx' in
        let (Refl, _) = pfInOut pfy in
        Ret $ Inter $ rewrite plusZeroRightNeutral mx in
        (\v => let (p, q) = splitAt (nx + ny) v in let (r, _) = splitAt nx p in
        rewrite plusCommutative mx nx in r ++ q)

fork : {x : Shp} -> Ruby a (mkIn x, T [mkOut x, mkOut x])
fork {x} with (make (mkIn x)) proof mkx
    _ | ((n, m) ** _) with (make (mkOut x)) proof mkx'
     _ | ((n', m') ** _) =
        let pfx = sym $ cong fst mkx in
        let pfx' = cong fst mkx' in
        let pf = makepf2 {x=mkOut x} {y=mkOut x} (sym pfx') (sym pfx') in
        let (Refl, pf') = pfInOut {x=x} pfx in
        let (Refl, Refl) = splitPf $ trans pf' pfx' in
        Ret $ Inter (rewrite plusZeroRightNeutral n in (\v => v ++ v))

rsh : {x,y,z : DShp} -> Ruby a (T [x, T [y, z]], T [T [compl x, compl y], compl z])
rsh {x,y,z} with (make x) proof mkx
    _ | ((nx, mx) ** _) with (make y) proof mky
     _ | ((ny, my) ** _) with (make z) proof mkz
      _ | ((nz, mz) ** _) with (make (compl x)) proof mkx'
       _ | ((nx', mx') ** _) with (make (compl y)) proof mky'
        _ | ((ny', my') ** _) with (make (compl z)) proof mkz'
         _ | ((nz', mz') ** _) =
            let (pfx, pfx') = (sym $ cong fst mkx, sym $ cong fst mkx') in
            let (pfy, pfy') = (sym $ cong fst mky, sym $ cong fst mky') in
            let (pfz, pfz') = (sym $ cong fst mkz, sym $ cong fst mkz') in
            let (Refl, Refl) = makepf' {x=x} pfx pfx' in
            let (Refl, Refl) = makepf' {x=y} pfy pfy' in
            let (Refl, Refl) = makepf' {x=z} pfz pfz' in
            let pfyz = makepf2 {x=y,y=z} pfy pfz in
            let pfxy' = makepf2 {x=compl x,y=compl y} pfx' pfy' in
            let pfx_yz = makepf2 {x=x,y=T[y,z]} pfx pfyz in
            let pfxy_z' = makepf2 {x=T[compl x,compl y],y=compl z} pfxy' pfz' in
            Ret $ Inter (rewrite plusAssociative mx my mz in rewrite plusAssociative nx ny nz in
            rewrite plusCommutative ((mx+my)+mz) ((nx+ny)+nz) in id)

outl' : {x, y: DShp} -> {auto py : y = mkIn y} -> Ruby a (T [x, y], compl x)
outl' {x, y} with (make x) proof mkx
    _ | ((nx, mx) ** _) with (make (compl x)) proof mkx'
     _ | ((nx', mx') ** _) with (make y) proof mky
      _ | ((ny, my) ** _) =
        let pfx = sym $ cong fst mkx in
        let pfx' = sym $ cong fst mkx' in
        let pfy = sym $ cong fst mky in
        let z = makepf2 {x=x} {y=y} pfx pfy in
        let (Refl, Refl) = makepf' pfx pfx' in
        let aaa = replace {p=replmk (ny, my)} py pfy in
        let (pfmy, _) = pfInOut aaa in
        Ret $ Inter $ rewrite pfmy in rewrite plusZeroRightNeutral mx in
        (\v => let (p, q) = splitAt (nx + ny) v in let (r, _) = splitAt nx p in
        rewrite plusCommutative mx nx in r ++ q)

fork' : {x, y : DShp} -> {auto pin : x = mkIn x} -> {auto pout : y = mkOut x} -> Ruby a (x, T [y, y])
fork' {x, y, pin, pout} with (make x) proof mkx
    _ | ((n, m) ** _) with (make y) proof mky
     _ | ((n', m') ** _) =
        let pfx = sym $ cong fst mkx in
        let pfy = sym $ cong fst mky in
        let pfx' = replace {p=replmk (n, m)} pin pfx in
        let pfy' = replace {p=replmk (n', m')} pout pfy in
        let pf = makepf2 {x=y} {y=y} pfy pfy in
        let (pf1, pf2) = pfInOut {x=x} pfx' in
        let (pf3, pf4) = splitPf $ trans pf2 (sym pfy') in
        Ret $ Inter (rewrite pf1 in rewrite sym pf3 in rewrite pf4 in
        rewrite plusZeroRightNeutral m' in (\v => v ++ v))

fork1 : {x, y : DShp} -> {auto pin : x = mkIn x} -> {auto pout : y = mkOut x} -> Ruby a (y, T [x, y])
fork1 {x, y, pin, pout} with (make x) proof mkx
    _ | ((n, m) ** _) with (make y) proof mky
     _ | ((n', m') ** _) =
        let pfx = sym $ cong fst mkx in
        let pfy = sym $ cong fst mky in
        let pfx' = replace {p=replmk (n, m)} pin pfx in
        let pfy' = replace {p=replmk (n', m')} pout pfy in
        let pf = makepf2 {x=x} {y=y} pfx pfy in
        let (pf1, pf2) = pfInOut {x=x} pfx' in
        let (pf3, pf4) = splitPf $ trans pf2 (sym pfy') in
        Ret $ Inter (rewrite pf1 in rewrite sym pf3 in rewrite pf4 in
        rewrite plusZeroRightNeutral m' in (\v => v ++ v))
-}

data Is : Dir -> Rose Dir -> Type where
    TIs : {xs : Vect n (Rose Dir)} -> HVect (map (Is d) xs) -> Is d (T xs)
    VIs : Is d (V d)

mk : Dir -> Rose a -> DShp
mk d = map (const d)

ispf : {d : Dir} -> Is d x -> x = mk d x
ispf VIs = Refl
ispf (TIs {xs=x::xs} (y::ys)) = let (pf, pfs) = (ispf y, ispf (TIs ys)) in cong T (addEq pf (underT pfs))
ispf (TIs {xs=[]} []) = Refl

simp : make x = ((n, m) ** p) -> (n, m) = fst (make x)
simp pf = sym $ cong fst pf

isinpf : Is In x -> (nx, mx) = fst (make x) -> mx = 0
isinpf VIs Refl = Refl
isinpf (TIs {xs=[]} []) Refl = Refl
isinpf (TIs {xs=x::xs} (h::hs)) pf with (make x) proof mkx
    _ | ((n, m) ** (Iss f g)) with (make (T xs)) proof mkxs
     _ | ((ns, ms) ** (Iss fs gs)) =
        let (Refl) = isinpf h (simp mkx) in
        let (Refl) = isinpf (TIs hs) (simp mkxs) in
        let (_, Refl) = splitPf pf in Refl

isoutpf : Is Out x -> (nx, mx) = fst (make x) -> nx = 0
isoutpf VIs Refl = Refl
isoutpf (TIs {xs=[]} []) Refl = Refl
isoutpf (TIs {xs=x::xs} (h::hs)) pf with (make x) proof mkx
    _ | ((n, m) ** (Iss f g)) with (make (T xs)) proof mkxs
     _ | ((ns, ms) ** (Iss fs gs)) =
        let (Refl) = isoutpf h (simp mkx) in
        let (Refl) = isoutpf (TIs hs) (simp mkxs) in
        let (Refl, _) = splitPf pf in Refl

data Same : Eq a => Rose a -> Rose a -> Type where
    TSame : Eq a => {xs, ys : Vect n (Rose a)} -> HVect (zipWith Same xs ys) -> Same (T xs) (T ys)
    VSame : Eq a => {x : a} -> Same (V x) (V x)

data Compl : DShp -> DShp -> Type where
    TCompl : {xs, ys : Vect n DShp} -> HVect (zipWith Compl xs ys) -> Compl (T xs) (T ys)
    VCompl1 : Compl (V In) (V Out)
    VCompl2 : Compl (V Out) (V In)

complpf : Compl x y -> y = compl x
complpf VCompl1 = Refl
complpf VCompl2 = Refl
complpf (TCompl {xs=(x::xs),ys=(y::ys)} (h::hs)) =
    let (pf, pfs) = (complpf h, complpf (TCompl hs)) in cong T (addEq pf (underT pfs))
complpf (TCompl {xs=[],ys=[]} []) = Refl

complSwap : Compl x y -> (nx, mx) = fst (make x) -> (ny, my) = fst (make y) -> (nx = my, ny = mx)
complSwap VCompl1 Refl Refl = (Refl, Refl)
complSwap VCompl2 Refl Refl = (Refl, Refl)
complSwap (TCompl {xs=[],ys=[]} []) Refl Refl = (Refl, Refl)
complSwap (TCompl {xs=x::xs,ys=y::ys} (h::hs)) pfx pfy with (make x) proof mkx
    _ | ((n, m) ** (Iss f g)) with (make y) proof mky
     _ | ((n', m') ** (Iss f' g')) with (make (T xs)) proof mkxs
      _ | ((ns, ms) ** (Iss fs gs)) with (make (T ys)) proof mkys
       _ | ((ns', ms') ** (Iss fs' gs')) =
        let (Refl, Refl) = complSwap h (simp mkx) (simp mky) in
        let (Refl, Refl) = complSwap (TCompl hs) (simp mkxs) (simp mkys) in
        let (Refl, Refl) = splitPf pfx in
        let (Refl, Refl) = splitPf pfy in
        (Refl, Refl)

fork2 : {x, y : DShp} -> {auto pin : Is In x} -> {auto pout : Is Out y} -> {auto pcompl : Compl x y} -> Ruby a (y, T [y, x])
fork2 {x, y, pin, pout, pcompl} with (make x) proof mkx
    _ | ((n, m) ** _) with (make y) proof mky
     _ | ((n', m') ** _) =
        let (pfx, pfy) = (simp mkx, simp mky) in
        let pfx' = replace {p=replmk (n, m)} (ispf pin) pfx in
        let pfy' = replace {p=replmk (n', m')} (ispf pout) pfy in
        let pf = makepf2 {x=y} {y=x} pfy pfx in
        let (Refl, Refl) = complSwap pcompl pfx pfy in
        let (Refl) = isinpf pin pfx in
        let (pf1, pf2) = (cong fst pfy, cong snd pfy) in
        Ret $ Inter (rewrite plusZeroRightNeutral n in
        replace {p=(\v => Vect (v + n) a -> Vect (snd ((make y).fst) + n) a)} pf1
        (rewrite pf2 in (\v => v ++ v)))

rsh' : {x,y,z,p,q,r : DShp} -> {xp : Compl x p} -> {yq : Compl y q} -> {zr : Compl z r} -> Ruby a (T [x, T [y, z]], T [T [p, q], r])
rsh' {x,y,z,p,q,r,xp,yq,zr} with (make x) proof mkx
    _ | ((nx, mx) ** _) with (make y) proof mky
     _ | ((ny, my) ** (Iss fy gy)) with (make z) proof mkz
      _ | ((nz, mz) ** (Iss fz gz)) with (make p) proof mkp
       _ | ((np, mp) ** _) with (make q) proof mkq
        _ | ((nq, mq) ** _) with (make r) proof mkr
         _ | ((nr, mr) ** _) =
            let (pfx, pfy, pfz) = (simp mkx, simp mky, simp mkz) in
            let (pfp, pfq, pfr) = (simp mkp, simp mkq, simp mkr) in
            let (Refl, Refl) = complSwap xp pfx pfp in
            let (Refl, Refl) = complSwap yq pfy pfq in
            let (Refl, Refl) = complSwap zr pfz pfr in
            let pfyz = makepf2 {x=y,y=z} pfy pfz in
            let pfpq = makepf2 {x=p,y=q} pfp pfq in
            let pfxyz = makepf2 {x=x,y=T[y,z]} pfx pfyz in
            let pfpqr = makepf2 {x=T[p,q],y=r} pfpq pfr in
            Ret $ Inter (rewrite plusAssociative mx my mz in rewrite plusAssociative nx ny nz in
            rewrite plusCommutative ((mx+my)+mz) ((nx+ny)+nz) in id)

--fork2 : Ruby a (T [O, I], T [T [O, O], I])
--fork2 = inv (outl') <:> (inv fork' <|> fork') <:> rsh

--p1 : Ruby a (T [O, I], T [T [I, O], I])
--p1 = inv outl'

--p2 : Ruby a (T [T [O, I], O], T [O, T [O, I]])
--p2 = inv fork2 <|> fork2

--p3 : Ruby a (T [O, I], T [O, T [O, I]])
--p3 = p1 <:> (inv fork2 <|> fork2)

--p4 : Ruby a (T [I, T [I, O]], T [T [O, O], I])
--p4 = rsh

--p5 : Ruby a (T [O, I], T [T [O, O], I])
--p5 = p1 <:> (inv fork2 <|> fork2) <:> rsh

--p6 : Ruby a (T [T [O, I], O], T [T [O, O], I])
--p6 = (inv fork2 <|> fork2) <:> p4

