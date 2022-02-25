module Lambda

import Effects.Algebraic

public export
data Lambda : (k : Type) -> Type where
    LLam : String -> k -> Lambda k
    LApp : k -> k -> Lambda k

public export
Functor Lambda where
    map f (LLam x k) = LLam x (f k)
    map f (LApp k1 k2) = LApp (f k1) (f k2)

public export
Show k => Show (Lambda k) where
    show (LLam v k) = "(λ" ++ show v ++ " -> " ++ show k ++ ")"
    show (LApp p q) = "(" ++ show p ++ " " ++ show q ++ ")"

public export
Show a => Show (Free Lambda a) where
    show (Var v) = show v
    show (Op (LLam v k)) = "(λ" ++ show v ++ " -> " ++ show k ++ ")"
    show (Op (LApp p q)) = "(" ++ show p ++ " " ++ show q ++ ")"

public export
Term : Type -> Type
Term a = Free Lambda a

public export
data TType : Type where
    TFree : String -> TType
    TFixed : String -> TType
    TFunc : TType -> TType -> TType

public export
Show TType where
    show (TFree x) = x
    show (TFixed x) = "{" ++ x ++ "}"
    show (TFunc a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"

public export
Eq TType where
    (TFree x) == (TFree y) = x == y
    (TFixed x) == (TFixed y) = x == y
    (TFunc a b) == (TFunc c d) = (a == c) && (b == d)
    _ == _ = False
