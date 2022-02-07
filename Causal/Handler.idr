module Causal.Handler

import Causal.Ruby
import Causal.Utils
import Causal.Properties

take' : (n  : Nat) -> Lazy (Vect (n + m) a) -> Lazy (Vect n a)
take' 0 xs = Nil
take' (S k) (x :: xs) = x :: take k xs

drop' : (n : Nat) -> Lazy (Vect (n + m) a) -> Lazy (Vect m a)
drop' 0 xs = xs
drop' (S k) (x :: xs) = drop k xs

handleSeq : Compl q q' => Interp a (p, q) -> Interp a (q', r) -> Interp a (p, r)
handleSeq (Inter {dl=p, dr=q,nl=(qnl,qml),nr=(qnr,qmr),pfl=qpfl,pfr=qpfr} qs)
    (Inter {dl=q',dr=r,nl=(rnl,rml),nr=(rnr,rmr),pfl=rpfl,pfr=rpfr} rs) =
        Inter {dl=p,dr=r,nl=(qnl,qml),nr=(rnr,rmr)} ss where
            eq1 : qnr = rml
            eq1 = fst (complSwap qpfr rpfl)
            eq2 : rnl = qmr
            eq2 = snd (complSwap qpfr rpfl)
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

handlePar : Interp a (p1, q1) -> Interp a (p2, q2) -> Interp a (T [p1, p2], T [q1, q2])
handlePar (Inter {dl=p1,dr=q1,nl=(qnl,qml),nr=(qnr,qmr),pfl=qpfl,pfr=qpfr} qs)
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

handleInv : Interp a (p, q) -> Interp a (q, p)
handleInv (Inter {dl=p,dr=q,nl=(nl,ml),nr=(nr,mr),pfl=pfl,pfr=pfr} qs) =
    Inter {dl=q,dr=p,nl=(nr,mr),nr=(nl,ml),pfl=pfr,pfr=pfl} ws where
    ws : Vect (nr + nl) a -> Vect (mr + ml) a
    ws vs =
        let (x, y) = splitAt nr vs in
        let (j, k) = splitAt ml (qs (y ++ x)) in
        k ++ j

alg : RComb (Interp a) x -> Interp a x
alg (Seq q r) = handleSeq q r
alg (Par q r) = handlePar q r
alg (Inv q) = handleInv q

public export
handle : {a : Type} -> IFree RComb (Interp a) x -> Interp a x
handle {a} = fold id alg
