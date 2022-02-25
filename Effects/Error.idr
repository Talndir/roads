module Effects.Error

import Effects.Algebraic

public export
data Error e k = Throw e

public export
Functor (Error e) where
    map _ (Throw x) = Throw x

public export
throw : (Error e) -< f => e -> Free f b
throw x = ins (Throw x)

gen_error : Gen a (Either e a)
gen_error = Right

alg_error : Alg (Error e) (Either e a)
alg_error (Throw x) = Left x

public export
handle_error : Handler (Error e) a (Either e a)
handle_error = handle gen_error alg_error


data ErrorH : Type -> Type -> (Type -> Type) -> Type where
    Error_H : m (Either e a) -> ErrorH e a m

runErrorH : ErrorH e a m -> m (Either e a)
runErrorH (Error_H x) = x

ModularCarrier (ErrorH e a) where
    fwd mf = Error_H $ do f <- mf; runErrorH f

gen_errorH : Monad m => GenH a (ErrorH e a) m
gen_errorH x = Error_H $ pure (Right x)

alg_errorH : Monad m => AlgH (Error e) (ErrorH e a) m
alg_errorH (Throw x) = Error_H $ pure (Left x)

fin_errorH : Monad m => FinH (Either e a) (ErrorH e a) m
fin_errorH = runErrorH

public export
handle_errorH : Functor g => HandlerH (Error e) g a (Either e a)
handle_errorH = handleH' gen_errorH alg_errorH fin_errorH
