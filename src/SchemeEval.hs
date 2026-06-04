{-# LANGUAGE LambdaCase #-}

module SchemeEval where

import Control.Monad ((<=<))
import Control.Monad.Cont
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.IntMap as M
import qualified Data.Map.Strict as Env
import Data.Maybe (fromMaybe)
import SchemeParser
import SchemeTypes

runSchemeWith :: U -> S -> Scheme [E] -> A
runSchemeWith ρ σ ϕ =
  fromMaybe (error "Scheme computation failed") $
    runContT (runStateT (runReaderT (unScheme ϕ) ρ) σ) pure

runScheme :: Scheme [E] -> A
runScheme = runSchemeWith stdEnv stdStore

sputChar :: MonadIO m => Char -> SchemeT m u r s ()
sputChar = liftIO . putChar

sputStrLn :: MonadIO m => String -> SchemeT m u r s ()
sputStrLn = liftIO . putStrLn

eval :: Expr -> Scheme [E]
eval = evalM

evalM :: Expr -> Scheme [E]
evalM (Const a) = sendM (Ek a)
evalM (Id i) = do
  ρ <- ask
  ε <- holdM (envLookup ρ i)
  case ε of
    Em Undefined -> wrongM ("Undefined variable: " <> i)
    ε' -> sendM ε'
evalM (App e0 εs) = do
  εs' <- unpermute <$> evalsM (permute (e0 : εs))
  case εs' of
    (ϕ:args) -> applicateM ϕ args
    [] -> wrongM "application with no operator"
evalM (If ε0 ε1 ε2) = do
  ε <- singleM =<< evalM ε0
  if truish ε
    then evalM ε1
    else evalM ε2
evalM (IfPartial ε0 ε1) = do
  ε <- singleM =<< evalM ε0
  if truish ε
    then evalM ε1
    else sendM (Em Unspecified)
evalM (Lambda is gs e0) = do
  ρ <- ask
  α <- alloc (Em Unspecified)
  sendM (Ef (α, ϕ ρ))
  where
    ϕ ρ εs =
      if length εs == length is
        then do
          αs <- tievalsM εs
          local (const (extends ρ is αs)) (evalcM gs >> evalM e0)
        else
          wrongM
            ( "wrong number of arguments, expected "
                <> show (length is)
                <> ", namely "
                <> show is
                <> " but got "
                <> show (length εs)
                <> " instead"
            )
evalM (LambdaV is i gs e0) = do
  ρ <- ask
  α <- alloc (Em Unspecified)
  sendM (Ef (α, ϕ ρ))
  where
    ϕ ρ εs =
      if length εs >= length is
        then do
          rest <- makeList (dropfirst εs (length is))
          αs <- tievalsM (takefirst εs (length is) <> [rest])
          local (const (extends ρ (is <> [i]) αs)) (evalcM gs >> evalM e0)
        else
          wrongM
            ("too few arguments, expected at least " <> show (length is) <> ", namely " <> show is)
evalM (LambdaVV i gs e0) = evalM (LambdaV [] i gs e0)
evalM (Set i e) = do
  ε <- singleM =<< evalM e
  ρ <- ask
  assignM (envLookup ρ i) ε
  sendM (Em Unspecified)

-- |Evaluate a list of expressions, collecting one value from each.
evalsM :: [Expr] -> Scheme [E]
evalsM = mapM (singleM <=< evalM)

-- |Evaluate a list of commands, discarding each command's values.
evalcM :: [Expr] -> Scheme ()
evalcM = mapM_ evalM

-- |Look up an identifier in the environment.
envLookup :: U -> Ide -> L
envLookup ρ i = fromMaybe 0 (Env.lookup i ρ)

-- |Extend an environment with a list of identifiers and their store
-- locations.
extends :: U -> [Ide] -> [L] -> U
extends ρ is αs = Env.fromList (zip is αs) <> ρ

-- |Send a value to the current continuation.
sendM :: E -> Scheme [E]
sendM ε = pure [ε]

-- |Raise an error.
wrongM :: String -> Scheme a
wrongM = error

-- |Given a location, look it up in the store.
holdM :: L -> Scheme E
holdM α = do
  (_, σ) <- get
  pure (fst (σ M.! α))

singleM :: [E] -> Scheme E
singleM εs =
  if length εs == 1
    then pure (singleValue εs)
    else wrongM ("wrong number of return values, expected 1 but got " <> show (length εs))

singleValue :: [E] -> E
singleValue εs =
  if length εs == 1
    then
      case εs of
        ε:_ -> ε
        [] -> error "singleValue: empty value list"
    else error ("wrong number of return values, expected 1 but got " <> show (length εs))

-- |Given the store, return the next free cell.
new :: S -> L
new (c, _) = c + 1

-- |The empty environment.
emptyEnv :: U
emptyEnv = mempty

-- |The empty store.
emptyStore :: S
emptyStore = (0, mempty)

update :: L -> E -> S -> S
update α ε (c, σ) = (max α c, M.insert α (ε, True) σ)

alloc :: E -> Scheme L
alloc ε = do
  σ <- get
  let α = new σ
  put (update α ε σ)
  pure α

assignM :: L -> E -> Scheme ()
assignM α ε = modify (update α ε)

truish :: E -> T
truish (Ek (Boolean False)) = False
truish _ = True

-- |Permute an expression list (as the order of evaluation of
-- arguments is undefined in Scheme).  Must be an inverse operation to
-- @unpermute@.
permute :: [Expr] -> [Expr]
permute = id

-- |Unpermute a value list (as the order of evaluation of arguments is
-- undefined in Scheme).  Must be an inverse operation to @permute@.
unpermute :: [E] -> [E]
unpermute = id

-- |Apply a Scheme procedure to a list of operands.
applicateM :: E -> [E] -> Scheme [E]
applicateM (Ef (_, ϕ)) εs = ϕ εs
applicateM χ _ = wrongM ("failed to apply " <> show χ <> ", expected a procedure")

-- |Lift a Haskell function that takes one argument into a Scheme
-- procedure.
oneargM :: (E -> Scheme [E]) -> [E] -> Scheme [E]
oneargM ϕ [ε] = ϕ ε
oneargM _ εs = wrongM ("wrong number of arguments, expected 1 but got " <> show (length εs))

-- |Lift a Haskell function that takes two arguments into a Scheme
-- procedure.
twoargM :: (E -> E -> Scheme [E]) -> [E] -> Scheme [E]
twoargM ϕ [ε1, ε2] = ϕ ε1 ε2
twoargM _ εs =
  wrongM ("wrong number of arguments, expected 2 but got " <> show (length εs) <> ": " <> show εs)

makePair :: E -> E -> Scheme E
makePair ε1 ε2 = do
  α <- alloc ε1
  β <- alloc ε2
  pure (Ep (α, β, True))

-- |Scheme @list@.
list :: [E] -> Scheme [E]
list = fmap pure . makeList

makeList :: [E] -> Scheme E
makeList [] = pure (Ek Nil)
makeList (ε:εs) = do
  rest <- makeList εs
  makePair ε rest

-- |Scheme @cons@.
cons :: [E] -> Scheme [E]
cons = twoargM (\ε1 ε2 -> sendM =<< makePair ε1 ε2)

factorial :: [E] -> Scheme [E]
factorial =
  oneargM
    ( \case
        Ek (Number 0) -> sendM (Ek (Number 1))
        m@(Ek (Number n)) -> do
          ε <- singleM =<< factorial [Ek (Number (n - 1))]
          mult [ε, m]
        χ -> wrongM ("non-numeric argument to factorial" <> show χ)
    )

makeNumBinop :: String -> (Integer -> E) -> (Integer -> Integer -> Integer) -> [E] -> Scheme [E]
makeNumBinop name constructor op =
  twoargM
    ( \ε1 ε2 ->
        case ε1 of
          Ek (Number r1) ->
            case ε2 of
              Ek (Number r2) -> sendM (constructor (op r1 r2))
              χ -> wrongM ("non-numeric argument to " <> name <> ", got " <> show χ <> " instead")
          χ -> wrongM ("non-numeric argument to " <> name <> ", got " <> show χ <> " instead")
    )

makeNumPredicate :: String -> (Integer -> Integer -> Bool) -> [E] -> Scheme [E]
makeNumPredicate name op =
  twoargM
    ( \ε1 ε2 ->
        case ε1 of
          Ek (Number r1) ->
            case ε2 of
              Ek (Number r2) -> retbool (op r1 r2)
              χ -> wrongM ("non-numeric argument to " <> name <> ", got " <> show χ <> " instead")
          χ -> wrongM ("non-numeric argument to " <> name <> ", got " <> show χ <> " instead")
    )

-- |Scheme @+@
add :: [E] -> Scheme [E]
add = makeNumBinop "+" (Ek . Number) (+)

-- |Scheme @<@
less :: [E] -> Scheme [E]
less = makeNumPredicate "<" (<)

-- |Scheme @>@
more :: [E] -> Scheme [E]
more = makeNumPredicate ">" (>)

-- |Scheme @=@
eqli :: [E] -> Scheme [E]
eqli = makeNumPredicate "=" (==)

-- |Scheme @>=@
eqlig :: [E] -> Scheme [E]
eqlig = makeNumPredicate ">=" (>=)

-- |Scheme @<=@
eqlilt :: [E] -> Scheme [E]
eqlilt = makeNumPredicate "<=" (<=)

-- |Scheme @*@
mult :: [E] -> Scheme [E]
mult = makeNumBinop "*" (Ek . Number) (*)

-- |Scheme @-@
sub :: [E] -> Scheme [E]
sub = makeNumBinop "-" (Ek . Number) (-)

-- |Scheme @modulo@
smod :: [E] -> Scheme [E]
smod = makeNumBinop "modulo" (Ek . Number) mod

-- |Scheme @div@
sdiv :: [E] -> Scheme [E]
sdiv = makeNumBinop "div" (Ek . Number) div

-- |Scheme @car@
car :: [E] -> Scheme [E]
car = oneargM (sendM <=< carValue)

carValue :: E -> Scheme E
carValue =
  \case
    Ep (α, _, _) -> holdM α
    χ -> wrongM ("non-pair argument to car: " <> show χ)

-- |Scheme @cdr@
cdr :: [E] -> Scheme [E]
cdr = oneargM (sendM <=< cdrValue)

cdrValue :: E -> Scheme E
cdrValue =
  \case
    Ep (_, α, _) -> holdM α
    χ -> wrongM ("non-pair argument to cdr: " <> show χ)

-- |Scheme @set-car!@
setcar :: [E] -> Scheme [E]
setcar =
  twoargM
    ( \ε1 ε2 ->
        case ε1 of
          Ep (α, _, True) -> assignM α ε2 >> sendM (Em Unspecified)
          Ep _ -> wrongM "immutable argument to set-car!"
          χ -> wrongM ("non-pair argument to set-cdr!: " <> show χ)
    )

-- |Scheme @set-cdr!@
setcdr :: [E] -> Scheme [E]
setcdr =
  twoargM
    ( \ε1 ε2 ->
        case ε1 of
          Ep (_, α, True) -> assignM α ε2 >> sendM (Em Unspecified)
          Ep _ -> wrongM "immutable argument to set-cdr!"
          χ -> wrongM ("non-pair argument to set-cdr! got " <> show χ)
    )

-- |Scheme @eqv?@
eqv :: [E] -> Scheme [E]
eqv =
  twoargM
    ( \ε1 ε2 ->
        case (ε1, ε2) of
          (Ek α, Ek β) -> retbool (α == β)
          (Em α, Em β) -> retbool (α == β)
          (Ev α, Ev β) -> retbool (α == β)
          (Ep (α, x, _), Ep (β, y, _)) -> retbool (α == β && x == y)
          (Ef (α, _), Ef (β, _)) -> retbool (α == β)
          _ -> retbool False
    )

retbool :: Bool -> Scheme [E]
retbool = sendM . Ek . Boolean

predLift :: (E -> Bool) -> [E] -> Scheme [E]
predLift p = oneargM (retbool . p)

-- |Scheme @number?@
numberp :: [E] -> Scheme [E]
numberp = predLift p
  where
    p (Ek (Number _)) = True
    p _ = False

-- |Scheme @boolean?@
booleanp :: [E] -> Scheme [E]
booleanp = predLift p
  where
    p (Ek (Boolean _)) = True
    p _ = False

-- |Scheme @symbol?@
symbolp :: [E] -> Scheme [E]
symbolp = predLift p
  where
    p (Ek (Symbol _)) = True
    p _ = False

-- |Scheme @procedure?@
procedurep :: [E] -> Scheme [E]
procedurep = predLift p
  where
    p (Ef _) = True
    p _ = False

-- |Scheme @pair?@
pairp :: [E] -> Scheme [E]
pairp = predLift p
  where
    p (Ep _) = True
    p _ = False

-- |Scheme @null?@
nullp :: [E] -> Scheme [E]
nullp = predLift p
  where
    p (Ek Nil) = True
    p _ = False

-- |Scheme @string?@
stringp :: [E] -> Scheme [E]
stringp = predLift p
  where
    p (Ek (String _)) = True
    p _ = False

-- |Scheme @symbol->string@
symbolToString :: [E] -> Scheme [E]
symbolToString =
  oneargM
    ( \case
        Ek (Symbol q) -> sendM (Ek (String q))
        χ -> wrongM ("non-symbol argument to symbol->string: " <> show χ)
    )

-- |Scheme @string->symbol@
stringToSymbol :: [E] -> Scheme [E]
stringToSymbol =
  oneargM
    ( \case
        Ek (String q) -> sendM (Ek (Symbol q))
        χ -> wrongM ("non-string argument to string->symbol: " <> show χ)
    )

-- |Scheme @string-append@
stringAppend :: [E] -> Scheme [E]
stringAppend =
  twoargM
    ( \ε1 ε2 ->
        case (ε1, ε2) of
          (Ek (String p), Ek (String q)) -> sendM (Ek (String (p <> q)))
          (χ, Ek (String _)) -> wrongM ("non-string argument to string-append: " <> show χ)
          (Ek (String _), χ) -> wrongM ("non-string argument to string-append: " <> show χ)
          (χ, χ') -> wrongM ("non-string arguments to string-append: " <> show χ <> " " <> show χ')
    )

-- |Scheme @number->string@
numberToString :: [E] -> Scheme [E]
numberToString =
  oneargM
    ( \case
        Ek (Number n) -> sendM (Ek (String (show n)))
        χ -> wrongM ("non-numeric argument to number->string: " <> show χ)
    )

liftExpr :: Expr -> [E] -> Scheme [E]
liftExpr = applicateM . singleValue . fst . evalStd

liftString :: String -> [E] -> Scheme [E]
liftString = liftExpr . rparse

-- |Parse and evaluate a string.
reval :: String -> A
reval s =
  case readProg s of
    Right res -> evalStd res
    Left err -> error ("Parse error: " <> show err)

-- |Parse a string into an expression.
rparse :: String -> Expr
rparse s =
  case readProg s of
    Right res -> res
    Left err -> error ("Parse error: " <> show err)

-- |An example of defining a Scheme procedure given an expression.
recursive :: [E] -> Scheme [E]
recursive =
  liftExpr
    ( Lambda
        ["fn"]
        []
        ( App
            (Lambda ["h"] [] (App (Id "h") [Id "h"]))
            [ Lambda
                ["g"]
                []
                ( App
                    (Id "fn")
                    [ LambdaVV
                        "arglist"
                        []
                        (App (Id "apply") [App (Id "g") [Id "g"], Id "arglist"])
                    ]
                )
            ]
        )
    )

-- |Scheme @apply@
apply :: [E] -> Scheme [E]
apply =
  twoargM
    ( \ε1 ε2 ->
        case ε1 of
          Ef _ -> valueslistM ε2 >>= applicateM ε1
          χ -> wrongM ("bad procedure argument to apply: " <> show χ)
    )

valueslistM :: E -> Scheme [E]
valueslistM =
  \case
    ε@(Ep _) -> do
      ε' <- carValue ε
      εs <- cdrValue ε >>= valueslistM
      pure (ε' : εs)
    Ek Nil -> pure []
    χ -> wrongM ("non-list argument to values-list:" <> show χ)

tievalsM :: [E] -> Scheme [L]
tievalsM = mapM alloc

-- |Scheme @call-with-current-continuation@
callcc :: [E] -> Scheme [E]
callcc =
  oneargM
    ( \ε ->
        case ε of
          Ef _ ->
            callCC $ \κ -> do
              α <- alloc (Em Unspecified)
              applicateM ε [Ef (α, κ)]
          _ -> wrongM ("bad procedure argument to call/cc: " <> show ε)
    )

-- |Scheme @values@
values :: [E] -> Scheme [E]
values = pure

-- |Scheme @call-with-values@
cwv :: [E] -> Scheme [E]
cwv = twoargM (\ε1 ε2 -> applicateM ε1 [] >>= applicateM ε2)

dropfirst :: [E] -> Int -> [E]
dropfirst εs v = drop v εs

takefirst :: [E] -> Int -> [E]
takefirst εs v = take v εs

-- |Evaluate an expression with the standard environment and store.
evalStd :: Expr -> A
evalStd prog = runSchemeWith stdEnv stdStore (evalM prog)

-- |The standard environment
stdEnv :: U
stdEnv = Env.fromList (zip stdEnvNames [1 ..])

exprDefinedOps :: [(String, [E] -> Scheme [E])]
exprDefinedOps = [("recursive", recursive)]

-- |The list of built-in operations.
builtInOps :: [(String, [E] -> Scheme [E])]
builtInOps =
  [ ("+", add)
  , ("*", mult)
  , ("-", sub)
  , ("/", sdiv)
  , ("modulo", smod)
  , ("<", less)
  , (">", more)
  , ("=", eqli)
  , (">=", eqlig)
  , ("<=", eqlilt)
  , ("cons", cons)
  , ("car", car)
  , ("cdr", cdr)
  , ("list", list)
  , ("eqv?", eqv)
  , ("boolean?", booleanp)
  , ("symbol?", symbolp)
  , ("procedure?", procedurep)
  , ("pair?", pairp)
  , ("number?", numberp)
  , ("set-car!", setcar)
  , ("set-cdr!", setcdr)
  , ("null?", nullp)
  , ("apply", apply)
  , ("call-with-values", cwv)
  , ("values", values)
  , ("call-with-current-continuation", callcc)
  , ("call/cc", callcc)
  , ("string?", stringp)
  , ("symbol->string", symbolToString)
  , ("string->symbol", stringToSymbol)
  , ("string-append", stringAppend)
  , ("number->string", numberToString)
  ]
    <> exprDefinedOps

-- |The list of names of standard operations.
stdEnvNames :: [String]
stdEnvNames = map fst builtInOps

-- |The list of standard operations.
stdOps :: [[E] -> Scheme [E]]
stdOps = map snd builtInOps

-- |The standard prelude.
stdPrelude :: S
stdPrelude = (n, M.fromList ((0, (Em Undefined, False)) : zipWith makeOpStore [1 ..] stdOps))
  where
    n = length stdOps + 1
    makeOpStore loc op = (loc, (Ef (loc, op), True))

-- |The standard store, consisting of a Prelude and infinite space.
stdStore :: S
stdStore = stdPrelude
