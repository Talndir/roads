module Effects.Reader

import Effects.Algebraic

public export
data Reader r k = Read (r -> k)

public export
Functor (Reader r) where
    map f (Read k) = Read (f . k)

public export
read : (Reader r) -< f => Free f r
read = ins (Read pure)

gen_reader : Gen a (r -> a)
gen_reader = const

alg_reader : Alg (Reader r) (r -> a)
alg_reader (Read k) = \r => k r r

public export
handle_reader : Handler (Reader r) a (r -> a)
handle_reader = handle gen_reader alg_reader


data ReaderH : Type -> Type -> (Type -> Type) -> Type where
    Reader_H : (r -> m a) -> ReaderH r a m

runReaderH : ReaderH r a m -> (r -> m a)
runReaderH (Reader_H x) = x

ModularCarrier (ReaderH r a) where
    fwd mf = Reader_H $ \r => do f <- mf; runReaderH f r

gen_readerH : Monad m => GenH a (ReaderH r a) m
gen_readerH x = Reader_H (\_ => pure x)

alg_readerH : Monad m => AlgH (Reader r) (ReaderH r a) m
alg_readerH (Read k) = Reader_H $ \r => runReaderH (k r) r

fin_readerH : Monad m => r -> FinH a (ReaderH r a) m
fin_readerH = flip runReaderH

public export
handle_readerH : Functor g => r -> HandlerH (Reader r) g a a
handle_readerH r = handleH' gen_readerH alg_readerH (fin_readerH r)
