module Causal.Blocks

import Data.Nat
import Causal.Ruby
import Causal.Utils
import Causal.Properties


replmk : (ns : (Nat, Nat)) -> (x : Rose Dir) -> Type
replmk ns x = ns = fst (make x)

public export
solve : (x : DShp) -> (y : DShp) -> Maybe (Compl x y)
solve (V In) (V Out) = pure VCompl1
solve (V Out) (V In) = pure VCompl2
solve (T (x :: xs)) (T (y :: ys)) = do
    c <- solve x y
    cs <- solve (T xs) (T ys)
    case cs of
        TCompl cs' => pure $ TCompl (c :: cs')
solve (T []) (T []) = pure $ TCompl []
solve _ _ = Nothing

fromIsJust : {x : Maybe a} -> IsJust x -> a
fromIsJust {x=Just x} t = x

export
fork2 : {x, y : DShp}
     -> {auto pin : Is In x} -> {auto pout : Is Out y} -> {auto pcompl : Compl x y}
     -> Ruby a (y, T [y, x])
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
rsh : {x,y,z,p,q,r : DShp}
    -> {auto xp : Compl x p} -> {auto yq : Compl y q} -> {auto zr : Compl z r}
    -> Ruby a (T [x, T [y, z]], T [T [p, q], r])
rsh {x,y,z,p,q,r,xp,yq,zr} with (make x) proof mkx
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

export
outl : {x, y, z: DShp}
    -> {auto pfin : Is In y} -> {auto pfc : Compl x z}
    -> Ruby a (T [x, y], z)
outl {x, y, pfin, pfc} with (make x) proof mkx
    _ | ((nx, mx) ** _) with (make z) proof mkz
     _ | ((nz, mz) ** _) with (make y) proof mky
      _ | ((ny, my) ** _) =
        let (pfx, pfy, pfz) = (simp mkx, simp mky, simp mkz)
            pfxy = makepf2 {x=x} {y=y} pfx pfy
            (Refl, Refl) = complSwap pfc pfx pfz
            (Refl) = isinpf pfin pfy
        in Ret $ Inter $ rewrite plusZeroRightNeutral mx in
        replace {p=(\v => Vect (nx+ny+v) a -> Vect (mx+snd(fst(make z))) a)} (cong fst pfz) $
        replace {p=(\v => Vect (nx+ny+mx) a -> Vect (mx+v) a)} (cong snd pfz)
        (\v => let (p, q) = splitAt (nx + ny) v in let (r, _) = splitAt nx p in
        rewrite plusCommutative mx nx in r ++ q)

p1 : Ruby a (T [O, I], T [T [I, O], I])
p1 = inv outl

p2 : Ruby a (T [T [O, I], O], T [O, T [O, I]])
p2 = inv fork2 <|> fork2

p4 : Ruby a (T [I, T [I, O]], T [T [O, O], I])
p4 = rsh

p : Ruby a (T [T [O, I], O], T [T [O, O], I])
p = p2 <:> p4

p6 : Ruby a (T [T [O, I], O], T [T [O, O], I])
p6 = (inv fork2 <|> fork2) <:> p4

qq : Ruby a (T [O, I], T [T [O, O], I])
qq = p1 <:> p6

-- Fails: Can't find an implementation
--p7 : Ruby a (T [O, I], T [T [O, O], I])
--p7 = inv outl <:> (inv fork2 <|> fork2) <:> rsh

--wooo : Ruby a (T [O, I], T [T [O, O], I])
--wooo = (inv (the (Ruby a (T [T [I, O], I], T [O, I])) outl)) <:>
--        (inv (the (Ruby a (O, T [O, I])) fork2) <|> (the (Ruby a (O, T [O, I])) fork2)) <:>
--        the (Ruby a (T [I, T [I, O]], T [T [O, O], I])) rsh
