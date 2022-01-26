module Causal.Blocks

import Data.Nat
import Causal.Ruby
import Causal.Utils
import Causal.Properties


replmk : (ns : (Nat, Nat)) -> (x : Rose Dir) -> Type
replmk ns x = ns = fst (make x)

export
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

export
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
