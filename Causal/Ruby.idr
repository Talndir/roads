module Causal.Ruby

import public IAE
import public Causal.Defs
import Causal.Utils

public export
data Isso : Shp -> Nat -> Nat -> Type where
    Iss : (f : forall b . Tuple ts b -> (Vect n b, Vect m b))
      -> (g : forall b . (Vect n b, Vect m b) -> Tuple ts b)
      -> Isso ts n m

public export
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

public export
data Interp : (a : Type) -> (ds : DShp') -> Type where
    Inter : {dl, dr : DShp} -> {nl, nr : (Nat, Nat)}
         -> {auto pfl : nl = fst (make dl)}
         -> {auto pfr : nr = fst (make dr)}
         -> (Vect (fst nl + fst nr) a -> Vect (snd nl + snd nr) a)
         -> Interp a (dl, dr)

public export
sim : Interp a (p, q) -> Typ (nil p, nil q) a -> Typ (nil p, nil q) a
sim (Inter {dl,dr,pfl=pfl@Refl,pfr=pfr@Refl} h) (x, y) with (make dl)
    _ | ((nl1, nl2) ** Iss fl gl) with (make dr)
     _ | ((nr1, nr2) ** (Iss fr gr)) =
        let (li, lo) = fl x in
        let (ri, ro) = fr y in
        let (rl, rr) = splitAt nl2 (h (li ++ ri)) in
        (gl (li, rl), gr (ri, rr))

public export
Ruby : Type -> DShp' -> Type
Ruby a x = IFree RComb (Interp a) x

infixl 3 <:>
public export
(<:>) : Compl b b' => Ruby t (a, b) -> Ruby t (b', c) -> Ruby t (a, c)
(q <:> r) = Do (Seq q r)

infixl 3 <|>
public export
(<|>) : Ruby t (a, b) -> Ruby t (c, d) -> Ruby t (T [a, c], T [b, d])
(q <|> r) = Do (Par q r)

public export
inv : Ruby t (a, b) -> Ruby t (b, a)
inv q = Do (Inv q)
