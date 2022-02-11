module Causal.Blocks

import Data.Nat
import Causal.Ruby
import Causal.Utils
import Causal.Properties

%hint
export
complIO : Compl x y => Ins x => Outs y

%hint
export
complOI : Compl x y => Outs y => Ins x

%hint
export
complCompl : Compl x y -> Compl y x

%hint
export
complIO' : Compl' xs ys => Ins' xs => Outs' ys

%hint
export
complOI' : Compl' xs ys => Outs' ys => Ins' xs

%hint
export
complCompl' : Compl' xs ys -> Compl' ys xs

%hint
export
oppIn : Opp x y -> Ins x

%hint
export
oppOut : Opp x y -> Outs y

%hint
export
oppCompl : Opp x y -> Compl x y

replmk : (ns : (Nat, Nat)) -> (x : Rose Dir) -> Type
replmk ns x = ns = fst (make x)

data Fork : (x : DShp) -> (y : DShp) -> (z : DShp) -> Type where
    [search x, search y, search z]
    Fork1 : Opp x y -> Fork x y y
    Fork2 : Opp x y -> Fork y x y
    Fork3 : Opp x y -> Fork y y x

fork : {x, y, z : DShp} -> Fork x y z => Ruby a (x, T [y, z])
fork {x,y,z=y} @{Fork1 opp} = ?f1
fork {x,y,z=x} @{Fork2 opp} = ?f2
fork {x,y=x,z} @{Fork3 opp} = ?f3

export
fork'' : {x, y : DShp} -> Opp x y => Ruby a (y, T [y, x])
fork'' {x, y} with (make x) proof mkx
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

fork1 : {x, y, z, w : DShp} -> Opp x y => Opp z w => Ruby a (T [T [y, x], w], T [T [y, w], z])
fork1 = (inv fork <|> fork) <:> rsh

fork2 : {x, y, z, w : DShp} -> Opp x y => Opp z w
     => Ruby a (T [y, x], T [T [y, w], z])
fork2 = inv outl <:> fork1

mux : {x, y : DShp} -> Opp x y => Ruby Bool (T [I, T [x, x]], y)
mux with (make x) proof mkx
    _ | ((nx, mx) ** (Iss fx gx)) with (make y) proof mky
     _ | ((ny, my) ** (Iss fy gy)) with (make (T [x, x])) proof mkxs
      _ | ((nxs, mxs) ** (Iss fxs gxs)) with (make (T [I, T [x, x]])) proof mkps
       _ | ((p, q) ** (Iss fp gp)) with (make I)
        _ | ((a, b) ** (Iss fa ga)) =
            let (pfx, pfy) = (simp mkx, simp mky)
                pf = makepf2 pfx pfx
                pf' = makepf2 {x=I} {y=T[x,x]} %search pf
                (Refl, Refl) = complSwap pfx pfy
                (Refl) = insPf pfx
                pf'' = cong fst pf'
            in Ret . Inter $ rewrite cong fst pfy in ?w
