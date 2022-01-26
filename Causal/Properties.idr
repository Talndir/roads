module Causal.Properties

import Causal.Ruby
import Causal.Utils
import Data.Nat

export
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

export
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

export
simp : make x = ((n, m) ** p) -> (n, m) = fst (make x)
simp pf = sym $ cong fst pf

export
ispf : {d : Dir} -> Is d x -> x = mk d x
ispf VIs = Refl
ispf (TIs {xs=x::xs} (y::ys)) = let (pf, pfs) = (ispf y, ispf (TIs ys)) in cong T (addEq pf (underT pfs))
ispf (TIs {xs=[]} []) = Refl

export
isinpf : Is In x -> (nx, mx) = fst (make x) -> mx = 0
isinpf VIs Refl = Refl
isinpf (TIs {xs=[]} []) Refl = Refl
isinpf (TIs {xs=x::xs} (h::hs)) pf with (make x) proof mkx
    _ | ((n, m) ** (Iss f g)) with (make (T xs)) proof mkxs
     _ | ((ns, ms) ** (Iss fs gs)) =
        let (Refl) = isinpf h (simp mkx) in
        let (Refl) = isinpf (TIs hs) (simp mkxs) in
        let (_, Refl) = splitPf pf in Refl

export
isoutpf : Is Out x -> (nx, mx) = fst (make x) -> nx = 0
isoutpf VIs Refl = Refl
isoutpf (TIs {xs=[]} []) Refl = Refl
isoutpf (TIs {xs=x::xs} (h::hs)) pf with (make x) proof mkx
    _ | ((n, m) ** (Iss f g)) with (make (T xs)) proof mkxs
     _ | ((ns, ms) ** (Iss fs gs)) =
        let (Refl) = isoutpf h (simp mkx) in
        let (Refl) = isoutpf (TIs hs) (simp mkxs) in
        let (Refl, _) = splitPf pf in Refl

export
complpf : Compl x y -> y = compl x
complpf VCompl1 = Refl
complpf VCompl2 = Refl
complpf (TCompl {xs=(x::xs),ys=(y::ys)} (h::hs)) =
    let (pf, pfs) = (complpf h, complpf (TCompl hs)) in cong T (addEq pf (underT pfs))
complpf (TCompl {xs=[],ys=[]} []) = Refl

export
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
