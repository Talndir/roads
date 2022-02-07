module Causal.Properties

import Causal.Ruby
import Causal.Utils
import Data.Nat

export
simp : make x = ((n, m) ** p) -> (n, m) = fst (make x)
simp pf = sym $ cong fst pf

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

mutual
    export
    complSwap : {x, y : DShp} -> Compl x y => (nx, mx) = fst (make x) -> (ny, my) = fst (make y) -> (nx = my, ny = mx)
    complSwap @{VComplIO} Refl Refl = (Refl, Refl)
    complSwap @{VComplOI} Refl Refl = (Refl, Refl)
    complSwap @{TCompl xs} pfx pfy = complSwap' pfx pfy
    
    complSwap' : {xs, ys : Vect k DShp} -> Compl' xs ys 
              => (nx, mx) = fst (make (T xs)) -> (ny, my) = fst (make (T ys))
              -> (nx = my, ny = mx)
    complSwap' @{VCompl'} Refl Refl = (Refl, Refl)
    complSwap' {xs=x::xs,ys=y::ys} @{TCompl' a as} pfx pfy with (make x) proof mkx
        _ | ((n, m) ** (Iss f g)) with (make y) proof mky
         _ | ((n', m') ** (Iss f' g')) with (make (T xs)) proof mkxs
          _ | ((ns, ms) ** (Iss fs gs)) with (make (T ys)) proof mkys
           _ | ((ns', ms') ** (Iss fs' gs')) =
                let (Refl, Refl) = complSwap (simp mkx) (simp mky)
                    (Refl, Refl) = complSwap' (simp mkxs) (simp mkys)
                    (Refl, Refl) = splitPf pfx
                    (Refl, Refl) = splitPf pfy
                in (Refl, Refl)

mutual
    export
    insPf : {x : DShp} -> Ins x => (nx, mx) = fst (make x) -> mx = 0
    insPf @{VIns} Refl = Refl
    insPf @{TIns xs} pf = insPf' pf

    insPf' : {xs : Vect k DShp} -> Ins' xs => (nx, mx) = fst (make (T xs)) -> mx = 0
    insPf' @{VIns'} Refl = Refl
    insPf' {xs=x::xs} @{TIns' a as} pf with (make x) proof mkx
        _ | ((n, m) ** (Iss f g)) with (make (T xs)) proof mkxs
         _ | ((ns, ms) ** (Iss fs gs)) =
            let (Refl) = insPf (simp mkx)
                (Refl) = insPf' (simp mkxs)
                (_, Refl) = splitPf pf in
            Refl
