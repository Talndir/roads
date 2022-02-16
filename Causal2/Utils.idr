module Causal2.Utils

import Causal2.Data

mutual
    %hint
    export
    oppLR : Opp x y -> Lefts x -> Rights y
    oppLR VOppLR VLefts = VRights
    oppLR (TOpp cs) (TLefts is) = TRights (oppLR' cs is)

    oppLR' : Opp' xs ys -> Lefts' xs -> Rights' ys
    oppLR' VOpp' VLefts' = VRights'
    oppLR' (TOpp' a as) (TLefts' b bs) = TRights' (oppLR a b) (oppLR' as bs)

mutual
    %hint
    export
    oppRL : Opp x y -> Rights y -> Lefts x
    oppRL VOppLR VRights = VLefts
    oppRL (TOpp cs) (TRights is) = TLefts (oppRL' cs is)

    oppRL' : Opp' xs ys -> Rights' ys -> Lefts' xs
    oppRL' VOpp' VRights' = VLefts'
    oppRL' (TOpp' a as) (TRights' b bs) = TLefts' (oppRL a b) (oppRL' as bs)

mutual
    %hint
    export
    oppOpp : Opp x y -> Opp y x
    oppOpp VOppLR = VOppRL
    oppOpp VOppRL = VOppLR
    oppOpp (TOpp cs) = TOpp (oppOpp' cs)

    oppOpp' : Opp' xs ys -> Opp' ys xs
    oppOpp' VOpp' = VOpp'
    oppOpp' (TOpp' a as) = TOpp' (oppOpp a) (oppOpp' as)

%hint
export
leftData : Lefts a => Data Right a
leftData @{VLefts} = RL
leftData @{TLefts VLefts'} = []
leftData @{TLefts (TLefts' t ts)} with (leftData @{t})
    _ | y with (leftData @{TLefts ts})
     _ | ys = y :: ys

%hint
export
rightData : Rights a => Data Left a
rightData @{VRights} = LR
rightData @{TRights VRights'} = []
rightData @{TRights (TRights' t ts)} with (rightData @{t})
    _ | y with (rightData @{TRights ts})
     _ | ys = y :: ys

export
empty : {d : Dir} -> (if d == Left then Rights x else Lefts x) => Data d x
empty {d=Right} = emptyL where
    emptyL : Lefts y => Data Right y
    emptyL @{VLefts} = RL
    emptyL @{TLefts VLefts'} = []
    emptyL @{TLefts (TLefts' t ts)} with (emptyL @{t})
        _ | v with (emptyL @{TLefts ts})
         _ | vs = v :: vs
empty {d=Left} = emptyR where
    emptyR : Rights y => Data Left y
    emptyR @{VRights} = LR
    emptyR @{TRights VRights'} = []
    emptyR @{TRights (TRights' t ts)} with (emptyR @{t})
        _ | v with (emptyR @{TRights ts})
         _ | vs = v :: vs

export
swap : {d : Dir} -> Opp z w => Data d z -> Data (swp d) w
swap {d=Left} p = swapL p where
    swapL : Opp x y => Data Left x -> Data Right y
    swapL @{VOppLR} (LL x) = RR x
    swapL @{VOppRL} LR = RL
    swapL @{TOpp VOpp'} _ = []
    swapL @{TOpp (TOpp' t ts)} (x :: xs) with (swapL @{t} x)
        _ | v with (swapL @{TOpp ts} xs)
         _ | vs = v :: vs
swap {d=Right} p = swapR p where
    swapR : Opp x y => Data Right x -> Data Left y
    swapR @{VOppRL} (RR x) = LL x
    swapR @{VOppLR} RL = LR
    swapR @{TOpp VOpp'} _ = []
    swapR @{TOpp (TOpp' t ts)} (x :: xs) with (swapR @{t} x)
        _ | v with (swapR @{TOpp ts} xs)
         _ | vs = v :: vs

export
copy : {d : Dir} -> Opp x y => Data d x
    -> (if d == Left then Lefts x else Rights x)
    => Data (swp d) y
copy {d} p = swap {d=d} p
