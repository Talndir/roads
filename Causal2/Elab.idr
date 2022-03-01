module Causal2.Elab

import public Language.Reflection
import public Language.Reflection.Syntax
import Language.Reflection.Pretty
import Text.PrettyPrint.Prettyprinter.Render.String
import Causal2.Typed

%language ElabReflection

printDoc : Doc ann -> String
printDoc = renderString . layoutPretty defaultLayoutOptions

splitArgs : List (Arg b) -> Elab (List (Arg b), List (Arg b))
splitArgs [] = pure ([], [])
splitArgs (x :: xs) = do
    (ys, zs) <- splitArgs xs
    case x of
        MkArg _ ImplicitArg _ _ => pure (x :: ys, zs)
        MkArg _ AutoImplicit _ _ => pure (ys, x :: zs)
        _ => fail $ "Function signature is not in the correct format"

resType : TTImp -> Elab TTImp
resType (IApp _ _ t) = pure t
resType x = fail $ "Function signature is not in the correct format: "-- ++ printDoc (pretty x)

getNames : List (Arg False) -> Elab (List Name)
getNames = traverse f where
    f : Arg False -> Elab Name
    f (MkArg _ _ Nothing _) = fail $ "Implicit argument missing name"
    f (MkArg _ _ (Just n) _) = pure n

convertCon : Arg False -> Elab (TTImp, Maybe (TTImp, TTImp, TTImp))
convertCon (MkArg _ _ _ t) = case t of
    IApp _ (IVar _ (NS _ "Lefts")) t => pure (`( << ~(t)), Nothing)
    IApp _ (IVar _ (NS _ "Rights")) t => pure (`( >> ~(t)), Nothing)
    IApp _ (IApp _ (IVar _ (NS _ "Opp")) t1) t2 => pure (`(~(t1) ~~ ~(t2)), Nothing)
    IApp _ (IApp _ (IApp _ (IVar _ (NS _ "Fork")) t1) t2) t3 => pure (`(Fk ~(t1) ~(t2) ~(t3)), Just (t1, t2, t3))
    x => fail $ "Can only use constraints Lefts, Rights and Opp: "-- ++ printDoc (pretty x)

vectOf : List TTImp -> TTImp
vectOf [] = `( Nil )
vectOf (x :: xs) = (`((::)) .$ x) .$ (vectOf xs)

makeLam : Clause -> TTImp
makeLam x = lambdaArg (MN "lamc" 0) .=> iCase (var (MN "lamc" 0)) implicitFalse [x]

makeInt : Integer -> TTImp
makeInt x = varStr "fromInteger" .$ primVal (BI x)

makeStr : String -> TTImp
makeStr x = varStr "fromString" .$ primVal (Str x)

dToN : TTImp -> TTImp
dToN (IApp _ (IApp _ (IVar _ (NS _ "Pair")) (IVar _ (NS _ "Typ"))) (IVar _ (NS _ "Dir"))) = var "Prelude.Nat"
dToN (IVar _ (NS _ "DShp")) = var "Causal2.Data.NShp"
dToN (IApp _ (IVar _ (NS _ "L"))  _) = var "Causal2.Data.V" .$ var "Prelude.Z"
dToN (IApp _ (IVar _ (NS _ "R"))  _) = var "Causal2.Data.V" .$ (var "Prelude.S" .$ var "Prelude.Z")
dToN (IApp _ x y) = dToN x .$ dToN y
dToN (INamedApp _ x n y) = INamedApp EmptyFC (dToN x) n (dToN y)
dToN w = w

dToT : TTImp -> TTImp
dToT (IApp _ (IApp _ (IVar _ (NS _ "Pair")) (IVar _ (NS _ "Typ"))) (IVar _ (NS _ "Dir"))) = var "Causal2.Data.Typ"
dToT (IVar _ (NS _ "DShp")) = var "Causal2.Data.TShp"
dToT (IApp _ (IVar _ (NS _ "L"))  x) = var "Causal2.Data.V" .$ x
dToT (IApp _ (IVar _ (NS _ "R"))  x) = var "Causal2.Data.V" .$ x
dToT (IApp _ x y) = dToT x .$ dToT y
dToT (INamedApp _ x n y) = INamedApp EmptyFC (dToT x) n (dToT y)
dToT w = w

applyNamed : TTImp -> List Name -> TTImp
applyNamed t [] = t
applyNamed t (x :: xs) = applyNamed (namedApp t x (var x)) xs

addT : TTImp -> TTImp
addT (IApp _ (IApp _ (INamedApp _ (INamedApp _ (IVar _ (NS (MkNS ("RoseSpace" :: _)) "::")) _ t1) n t2) x) y)
    = var "Causal2.Data.T" .$ (var "Data.Vect.::" .$ addT x .$ addT y)
addT (IApp _ x y) = addT x .$ addT y
addT (INamedApp _ x n y) = INamedApp EmptyFC (addT x) n (addT y)
addT w = w

makeUnique : List String -> TTImp -> TTImp
makeUnique ms = snd . makeUnique' [] where
    makeUnique' : List String -> TTImp -> (List String, TTImp)
    makeUnique' ns (IApp _ (IVar _ (NS _ "L"))  x) = (ns, implicitTrue)
    makeUnique' ns (IApp _ (IVar _ (NS _ "R"))  x) = (ns, implicitTrue)
    makeUnique' ns (IApp _ x y) =
        let (ns', x') = makeUnique' ns x
            (ns'', y') = makeUnique' ns' y in (ns'', x' .$ y')
    makeUnique' ns (INamedApp _ x n y) =
        let (ns', x') = makeUnique' ns x
            (ns'', y') = makeUnique' ns' y in (ns'', INamedApp EmptyFC x' n y')
    makeUnique' ns (IVar _ x) = let name = nameStr x in case name `elem` ms of
        False => (ns, var x)
        True => case (nameStr x) `elem` ns of
            True => (ns, implicitTrue)
            False => (name :: ns, var x)
    makeUnique' ns w = (ns, w)

getName : TTImp -> Maybe Name
getName (IVar _ n) = Just n
getName _ = Nothing

weird : List (TTImp, TTImp, TTImp) -> Elab (Name, Name, Name)
weird [] = pure (fromString "porcupine", fromString "banana", fromString "pineapple")
weird ((x, y, z) :: xs) = case r of
    Just q => pure q
    Nothing => fail $ "weird" where
        r : Maybe (Name, Name, Name)
        r = do
            x' <- getName x
            y' <- getName y
            z' <- getName z
            pure (x', y', z')

mapName : (Name -> Name) -> TTImp -> TTImp
mapName f (IVar _ n) = var (f n)
mapName f (IApp _ x y) = mapName f x .$ mapName f y
mapName f (INamedApp _ x m y) = INamedApp EmptyFC (mapName f x) m (mapName f y)
mapName _ w = w

replName : Name -> List Name -> TTImp -> TTImp
replName n ns = let ns' = map nameStr ns in mapName (\x => if (nameStr x) `elem` ns' then n else x)

removeName : Name -> List Name -> List Name
removeName n = filter (\x => nameStr x /= nameStr n)

getData : Name -> Elab (List Decl)
getData x = do
    (_, t) <- lookupName x
    let (ts, r) = unPi t
    (vs, cs) <- splitArgs ts
    res <- resType r
    ns <- getNames vs
    let boundNames = vectOf (map (bindVar . nameStr) ns)
    let varNames = vectOf (map var ns)
    cons' <- traverse convertCon cs
    let cons = map fst cons'
    (nn, n1, n2) <- weird (catMaybes (map snd cons'))
    let is = map (\n => MkArg MW ImplicitArg (Just n) (var "Causal2.Data.TShp")) (removeName n1 (removeName n2 ns))
    let bname = fromString ("Causal2.AUTOTYPED." ++ nameStr x)
    let tres = replName nn [n1, n2] (dToT res)
    let nv = makeInt . cast . length $ vs
    --fail . printDoc . pretty $ tres
    let sig = public' bname (piAll `(TBlock ~(tres)) is)
    
    let res' = makeUnique (map nameStr ns) . addT $ res

    --fail . printDoc . pretty $ res'

    let funcName = fromString ("Causal2.AUTOTYPED." ++ nameStr x ++ "_func")
    let funcSig = public' funcName `( forall a . (Rose a, Rose a) -> Vect ~(nv) (Rose a) )
    let funcBody = def funcName [
            var funcName .$ res' .= varNames,
            var funcName .$ `( _ ) .= `( replicate ~(nv) [] )
        ]
    
    --fail . printDoc . pretty $ funcBody

    let block = def bname [var bname .= `(
            MkTBlock
            ~(makeStr . nameStr $ x)
            ~(tres)
            ~(nv)
            ~(makeInt . cast . length $ cs)
            ~(makeLam (boundNames .= vectOf cons))
            ~(var funcName)
            ~(makeLam (boundNames .= res))
            ~(makeLam (boundNames .= dToN res))
            ~(makeLam (boundNames .= applyNamed (var x) ns))
        ) ]
    
    pure $ [funcSig, funcBody, sig, block]

public export
makeBlock : Name -> Elab ()
makeBlock n = do
    ds <- getData n
    declare ds

pi1 : {x, y : DShp} -> Rights y => DBlock (T [x, T [y, y]], R TInt)
fork : {x, y, z : DShp} -> Fork x y z => DBlock (x, [y, z])
--%runElab makeBlock `{fork}
