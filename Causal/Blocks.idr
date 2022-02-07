module Causal.Blocks

import Data.Nat
import Causal.Ruby
import Causal.Utils
import Causal.Properties

replmk : (ns : (Nat, Nat)) -> (x : Rose Dir) -> Type
replmk ns x = ns = fst (make x)

export
fork2 : {x, y : DShp} -> Opp x y => Ruby a (y, T [y, x])
fork2 {x, y} with (make x) proof mkx
    _ | ((n, m) ** _) with (make y) proof mky
     _ | ((n', m') ** _) =
        let (pfx, pfy) = (simp mkx, simp mky)
            pf = makepf2 {x=y} {y=x} pfy pfx
            (Refl, Refl) = complSwap pfx pfy
            (Refl) = insPf pfx
            (pf1, pf2) = (cong fst pfy, cong snd pfy) in
        Ret $ Inter (rewrite plusZeroRightNeutral n in
        replace {p=(\v => Vect (v + n) a -> Vect (snd ((make y).fst) + n) a)} pf1
        (rewrite pf2 in (\v => v ++ v)))

export
rsh : {x,y,z,p,q,r : DShp}
    -> Compl x p => Compl y q => Compl z r
    => Ruby a (T [x, T [y, z]], T [T [p, q], r])
rsh {x,y,z,p,q,r} with (make x) proof mkx
    _ | ((nx, mx) ** _) with (make y) proof mky
     _ | ((ny, my) ** (Iss fy gy)) with (make z) proof mkz
      _ | ((nz, mz) ** (Iss fz gz)) with (make p) proof mkp
       _ | ((np, mp) ** _) with (make q) proof mkq
        _ | ((nq, mq) ** _) with (make r) proof mkr
         _ | ((nr, mr) ** _) =
            let (pfx, pfy, pfz) = (simp mkx, simp mky, simp mkz)
                (pfp, pfq, pfr) = (simp mkp, simp mkq, simp mkr)
                (Refl, Refl) = complSwap pfx pfp
                (Refl, Refl) = complSwap pfy pfq
                (Refl, Refl) = complSwap pfz pfr
                pfyz = makepf2 {x=y,y=z} pfy pfz
                pfpq = makepf2 {x=p,y=q} pfp pfq
                pfxyz = makepf2 {x=x,y=T[y,z]} pfx pfyz
                pfpqr = makepf2 {x=T[p,q],y=r} pfpq pfr in
            Ret $ Inter (rewrite plusAssociative mx my mz in rewrite plusAssociative nx ny nz in
            rewrite plusCommutative ((mx+my)+mz) ((nx+ny)+nz) in id)

export
outl : {x, y, z: DShp}
    -> Ins y => Compl x z
    => Ruby a (T [x, y], z)
outl {x, y} with (make x) proof mkx
    _ | ((nx, mx) ** _) with (make z) proof mkz
     _ | ((nz, mz) ** _) with (make y) proof mky
      _ | ((ny, my) ** _) =
        let (pfx, pfy, pfz) = (simp mkx, simp mky, simp mkz)
            pfxy = makepf2 {x=x} {y=y} pfx pfy
            (Refl, Refl) = complSwap pfx pfz
            (Refl) = insPf pfy
        in Ret $ Inter $ rewrite plusZeroRightNeutral mx in
        replace {p=(\v => Vect (nx+ny+v) a -> Vect (mx+snd(fst(make z))) a)} (cong fst pfz) $
        replace {p=(\v => Vect (nx+ny+mx) a -> Vect (mx+v) a)} (cong snd pfz)
        (\v => let (p, q) = splitAt (nx + ny) v in let (r, _) = splitAt nx p in
        rewrite plusCommutative mx nx in r ++ q)

f2 : {x, y, z, w : DShp} -> Opp x y => Opp z w
  => Ruby a (T [y, x], T [T [y, w], z])
f2 = inv outl <:> (inv fork2 <|> fork2) <:> rsh
