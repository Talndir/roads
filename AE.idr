module AE

public export
data Free : (f : Type -> Type) -> (a : Type) -> Type where
    Var : a -> Free f a
    Op : f (Free f a) -> Free f a

public export
Functor f => Functor (Free f) where
    map f (Var x) = Var (f x)
    map f (Op op) = Op (map (map f) op)

public export
Functor f => Applicative (Free f) where
    pure = Var
    (Var f) <*> x = map f x
    (Op op) <*> x = Op (map (<*>x) op)

public export
Functor f => Monad (Free f) where
    (Var x) >>= f = f x
    (Op op) >>= f = Op (map (>>=f) op)

(Show a, Show (f (Free f a))) => Show (Free f a) where
    show (Var x) = show x
    show (Op op) = "(" ++ show op ++ ")"

public export
Gen : Type -> Type -> Type
Gen a b = a -> b

public export
Alg : (f : Type -> Type) -> Functor f => Type -> Type
Alg f b = f b -> b

public export
Handler : (f : Type -> Type) -> Functor f => Type -> Type -> Type
Handler f a b = Free f a -> b

public export
fold : Functor f => Gen a b -> Alg f b -> Handler f a b
fold gen _ (Var x) = gen x
fold gen alg (Op op) = alg (map (fold gen alg) op)

public export
handle : Functor f => Gen a b -> Alg f b -> Handler f a b
handle = fold

infixr 1 :+:
public export
data (:+:) : (f : Type -> Type) -> (g : Type -> Type) -> a -> Type where
    Inl : f a -> (f :+: g) a
    Inr : g a -> (f :+: g) a

public export
(Functor f, Functor g) => Functor (f :+: g) where
    map f (Inl x) = Inl (map f x)
    map f (Inr y) = Inr (map f y)

public export
liftl : (Functor f, Functor g) => Free f a -> Free (f :+: g) a
liftl (Var x) = Var x
liftl (Op op) = Op (map liftl (Inl op))

public export
liftr : (Functor f, Functor g) => Free f a -> Free (g :+: f) a
liftr (Var x) = Var x
liftr (Op op) = Op (map liftr (Inr op))

infixr 1 </>
public export
(</>) : (Functor f, Functor g) => Alg f b -> Alg g b -> Alg (f :+: g) b
(alg1 </> _) (Inl op) = alg1 op
(_ </> alg2) (Inr op) = alg2 op

infixr 1 -<
public export
interface (Functor f, Functor g) => (-<) f g where
    inj : f a -> g a
    proj : g a -> Maybe (f a)
    lift : Free f a -> Free g a

    ins : f (Free g a) -> Free g a
    ins = Op . inj
    
    ex : Free g a -> Maybe (f (Free g a))
    ex (Op x) = proj x
    ex (Var x) = Nothing

public export
(Functor f) => (-<) f f where
    inj = id
    proj = Just
    lift = id

public export
interface (Functor f, Functor g, Functor h) => HandleSum f g h where
    injsum : f a -> (g :+: h) a
    projsum : (g :+: h) a -> Maybe (f a)
    liftsum : Free f a -> Free (g :+: h) a

public export
(Functor f, Functor g, Functor h, f -< h) => HandleSum f g h where
    injsum = Inr . inj
    projsum (Inl x) = Nothing
    projsum (Inr y) = proj y
    liftsum = liftr . lift

public export
(Functor f, Functor h) => HandleSum f f h where
    injsum = Inl
    projsum (Inl x) = proj x
    projsum (Inr y) = Nothing
    liftsum = liftl

public export
(HandleSum f g h, Functor f) => (-<) f (g :+: h) where
    inj = injsum
    proj = projsum
    lift = liftsum
