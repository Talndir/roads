module Effects.Annotate

import Effects.Algebraic

public export
data Ann : (f : Type -> Type) -> (ann : Type) -> (a : Type) -> Type where
    An : (f a) -> ann -> Ann f ann a

public export
Functor f => Functor (Ann f ann) where
    map f (An x an) = An (map f x) an

public export
(Show (f a), Show ann) => Show (Ann f ann a) where
    show (An x y) = show x ++ " : " ++ show y

public export
annmap : Functor f => (a -> b) -> Free (Ann f a) c -> Free (Ann f b) c
annmap f (Op (An x a)) = Op (An (map (annmap f) x) (f a))
annmap f (Var x) = Var x

public export
annmap' : Functor f => (a -> b) -> Free (Ann f a) (c, a) -> Free (Ann f b) (c, b)
annmap' f x = map (map f) (annmap f x)

public export
getAnn : Free (Ann f ann) b -> Maybe ann
getAnn (Op (An _ t)) = Just t
getAnn (Var _) = Nothing

public export
getAnn' : Free (Ann f ann) (b, ann) -> ann
getAnn' (Op (An _ t)) = t
getAnn' (Var (_, t)) = t

public export
putAnn : Free (Ann f ann) b -> ann -> Free (Ann f ann) b
putAnn (Op (An x _)) t = Op (An x t)
putAnn (Var x) _ = Var x

public export
putAnn' : Free (Ann f ann) (b, ann) -> ann -> Free (Ann f ann) (b, ann)
putAnn' (Op (An x _)) t = Op (An x t)
putAnn' (Var (x, _)) t = Var (x, t)

public export
stripAnn : Functor f => Handler (Ann f a) b (Free f b)
stripAnn = handle Var (\(An x _) => Op x)

public export
stripAnn' : Functor f => Handler (Ann f a) (b, a) (Free f b)
stripAnn' = handle (\(x, _) => Var x) (\(An x _) => Op x)
