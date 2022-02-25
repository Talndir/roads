module Effects.State

import Effects.Algebraic

public export
data State s k
    = Get (s -> k)
    | Put s k

public export
Functor (State s) where
    map f (Get g) = Get (f . g)
    map f (Put s k) = Put s (f k)

public export
get : (State s) -< f => Free f s
get = ins (Get pure)

public export
put : (State s) -< f => s -> Free f ()
put s = ins (Put s (pure ()))

public export
gen_s : Gen a (s -> a)
gen_s a = \_ => a

public export
alg_s : Alg (State s) (s -> a)
alg_s (Get k) = \s => k s s
alg_s (Put s k) = \_ => k s

public export
handle_state : Handler (State s) a (s -> a)
handle_state = handle gen_s alg_s
