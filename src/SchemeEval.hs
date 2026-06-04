{-# LANGUAGE LambdaCase #-}

module SchemeEval where

import Control.Monad ((<=<))
import Control.Monad.Cont
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.IntMap as M
import Data.Maybe (fromMaybe)
import SchemeParser
import SchemeTypes

runSchemeWith :: U -> S -> Scheme [E] -> A
runSchemeWith u s f =
  fromMaybe (error "Scheme computation failed") $
    runContT (runStateT (runReaderT (unScheme f) u) s) pure

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
  p <- ask
  r <- holdM (envLookup p i)
  case r of
    Em Undefined -> wrongM ("Undefined variable: " <> i)
    e -> sendM e
evalM (App e0 es) = do
  vals <- unpermute <$> evalsM (permute (e0 : es))
  case vals of
    (f:args) -> applicateM f args
    [] -> wrongM "application with no operator"
evalM (If e0 e1 e2) = do
  e <- singleM =<< evalM e0
  if truish e
    then evalM e1
    else evalM e2
evalM (IfPartial e0 e1) = do
  e <- singleM =<< evalM e0
  if truish e
    then evalM e1
    else sendM (Em Unspecified)
evalM (Lambda is gs e0) = do
  p <- ask
  l <- alloc (Em Unspecified)
  sendM (Ef (l, f p))
  where
    f p es =
      if length es == length is
        then do
          as <- tievalsM es
          local (const (extends p is as)) (evalcM gs >> evalM e0)
        else
          wrongM
            ( "wrong number of arguments, expected "
                <> show (length is)
                <> ", namely "
                <> show is
                <> " but got "
                <> show (length es)
                <> " instead"
            )
evalM (LambdaV is i gs e0) = do
  p <- ask
  l <- alloc (Em Unspecified)
  sendM (Ef (l, f p))
  where
    f p es =
      if length es >= length is
        then do
          rest <- makeList (dropfirst es (length is))
          as <- tievalsM (takefirst es (length is) <> [rest])
          local (const (extends p (is <> [i]) as)) (evalcM gs >> evalM e0)
        else
          wrongM
            ("too few arguments, expected at least " <> show (length is) <> ", namely " <> show is)
evalM (LambdaVV i gs e0) = evalM (LambdaV [] i gs e0)
evalM (Set i e) = do
  v <- singleM =<< evalM e
  p <- ask
  assignM (envLookup p i) v
  sendM (Em Unspecified)

-- |Evaluate a list of expressions, collecting one value from each.
evalsM :: [Expr] -> Scheme [E]
evalsM = mapM (singleM <=< evalM)

-- |Evaluate a list of commands, discarding each command's values.
evalcM :: [Expr] -> Scheme ()
evalcM = mapM_ evalM

-- |Look up an identifier in the environment.
envLookup :: U -> Ide -> L
envLookup u i = fromMaybe 0 (lookup i u)

-- |Extend an environment with a list of identifiers and their store
-- locations.
extends :: U -> [Ide] -> [L] -> U
extends p is as = zip is as <> p

-- |Send a value to the current continuation.
sendM :: E -> Scheme [E]
sendM e = pure [e]

-- |Raise an error.
wrongM :: String -> Scheme a
wrongM = error

-- |Given a location, look it up in the store.
holdM :: L -> Scheme E
holdM a = do
  (_, m) <- get
  pure (fst (m M.! a))

singleM :: [E] -> Scheme E
singleM es =
  if length es == 1
    then pure (singleValue es)
    else wrongM ("wrong number of return values, expected 1 but got " <> show (length es))

singleValue :: [E] -> E
singleValue es =
  if length es == 1
    then
      case es of
        e:_ -> e
        [] -> error "singleValue: empty value list"
    else error ("wrong number of return values, expected 1 but got " <> show (length es))

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
update a e (c, s) = (max a c, M.insert a (e, True) s)

alloc :: E -> Scheme L
alloc e = do
  s <- get
  let a = new s
  put (update a e s)
  pure a

assignM :: L -> E -> Scheme ()
assignM a e = modify (update a e)

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
applicateM (Ef (_, f)) es = f es
applicateM x _ = wrongM ("failed to apply " <> show x <> ", expected a procedure")

-- |Lift a Haskell function that takes one argument into a Scheme
-- procedure.
oneargM :: (E -> Scheme [E]) -> [E] -> Scheme [E]
oneargM f [e] = f e
oneargM _ es = wrongM ("wrong number of arguments, expected 1 but got " <> show (length es))

-- |Lift a Haskell function that takes two arguments into a Scheme
-- procedure.
twoargM :: (E -> E -> Scheme [E]) -> [E] -> Scheme [E]
twoargM f [e1, e2] = f e1 e2
twoargM _ es =
  wrongM ("wrong number of arguments, expected 2 but got " <> show (length es) <> ": " <> show es)

makePair :: E -> E -> Scheme E
makePair e1 e2 = do
  a <- alloc e1
  b <- alloc e2
  pure (Ep (a, b, True))

-- |Scheme @list@.
list :: [E] -> Scheme [E]
list = fmap pure . makeList

makeList :: [E] -> Scheme E
makeList [] = pure (Ek Nil)
makeList (e:es) = do
  rest <- makeList es
  makePair e rest

-- |Scheme @cons@.
cons :: [E] -> Scheme [E]
cons = twoargM (\e1 e2 -> sendM =<< makePair e1 e2)

factorial :: [E] -> Scheme [E]
factorial =
  oneargM
    ( \case
        Ek (Number 0) -> sendM (Ek (Number 1))
        m@(Ek (Number n)) -> do
          e <- singleM =<< factorial [Ek (Number (n - 1))]
          mult [e, m]
        x -> wrongM ("non-numeric argument to factorial" <> show x)
    )

makeNumBinop :: String -> (Integer -> E) -> (Integer -> Integer -> Integer) -> [E] -> Scheme [E]
makeNumBinop name constructor op =
  twoargM
    ( \e1 e2 ->
        case e1 of
          Ek (Number r1) ->
            case e2 of
              Ek (Number r2) -> sendM (constructor (op r1 r2))
              x -> wrongM ("non-numeric argument to " <> name <> ", got " <> show x <> " instead")
          x -> wrongM ("non-numeric argument to " <> name <> ", got " <> show x <> " instead")
    )

makeNumPredicate :: String -> (Integer -> Integer -> Bool) -> [E] -> Scheme [E]
makeNumPredicate name op =
  twoargM
    ( \e1 e2 ->
        case e1 of
          Ek (Number r1) ->
            case e2 of
              Ek (Number r2) -> retbool (op r1 r2)
              x -> wrongM ("non-numeric argument to " <> name <> ", got " <> show x <> " instead")
          x -> wrongM ("non-numeric argument to " <> name <> ", got " <> show x <> " instead")
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
    Ep (a, _, _) -> holdM a
    x -> wrongM ("non-pair argument to car: " <> show x)

-- |Scheme @cdr@
cdr :: [E] -> Scheme [E]
cdr = oneargM (sendM <=< cdrValue)

cdrValue :: E -> Scheme E
cdrValue =
  \case
    Ep (_, a, _) -> holdM a
    x -> wrongM ("non-pair argument to cdr: " <> show x)

-- |Scheme @set-car!@
setcar :: [E] -> Scheme [E]
setcar =
  twoargM
    ( \e1 e2 ->
        case e1 of
          Ep (a, _, True) -> assignM a e2 >> sendM (Em Unspecified)
          Ep _ -> wrongM "immutable argument to set-car!"
          x -> wrongM ("non-pair argument to set-cdr!: " <> show x)
    )

-- |Scheme @set-cdr!@
setcdr :: [E] -> Scheme [E]
setcdr =
  twoargM
    ( \e1 e2 ->
        case e1 of
          Ep (_, a, True) -> assignM a e2 >> sendM (Em Unspecified)
          Ep _ -> wrongM "immutable argument to set-cdr!"
          x -> wrongM ("non-pair argument to set-cdr! got " <> show x)
    )

-- |Scheme @eqv?@
eqv :: [E] -> Scheme [E]
eqv =
  twoargM
    ( \e1 e2 ->
        case (e1, e2) of
          (Ek a, Ek b) -> retbool (a == b)
          (Em a, Em b) -> retbool (a == b)
          (Ev a, Ev b) -> retbool (a == b)
          (Ep (a, x, _), Ep (b, y, _)) -> retbool (a == b && x == y)
          (Ef (a, _), Ef (b, _)) -> retbool (a == b)
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
        v -> wrongM ("non-symbol argument to symbol->string: " <> show v)
    )

-- |Scheme @string->symbol@
stringToSymbol :: [E] -> Scheme [E]
stringToSymbol =
  oneargM
    ( \case
        Ek (String q) -> sendM (Ek (Symbol q))
        v -> wrongM ("non-string argument to string->symbol: " <> show v)
    )

-- |Scheme @string-append@
stringAppend :: [E] -> Scheme [E]
stringAppend =
  twoargM
    ( \e1 e2 ->
        case (e1, e2) of
          (Ek (String p), Ek (String q)) -> sendM (Ek (String (p <> q)))
          (x, Ek (String _)) -> wrongM ("non-string argument to string-append: " <> show x)
          (Ek (String _), x) -> wrongM ("non-string argument to string-append: " <> show x)
          (x, x') -> wrongM ("non-string arguments to string-append: " <> show x <> " " <> show x')
    )

-- |Scheme @number->string@
numberToString :: [E] -> Scheme [E]
numberToString =
  oneargM
    ( \case
        Ek (Number n) -> sendM (Ek (String (show n)))
        x -> wrongM ("non-numeric argument to number->string: " <> show x)
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
    ( \e1 e2 ->
        case e1 of
          Ef _ -> valueslistM e2 >>= applicateM e1
          x -> wrongM ("bad procedure argument to apply: " <> show x)
    )

valueslistM :: E -> Scheme [E]
valueslistM =
  \case
    e@(Ep _) -> do
      x <- carValue e
      xs <- cdrValue e >>= valueslistM
      pure (x : xs)
    Ek Nil -> pure []
    x -> wrongM ("non-list argument to values-list:" <> show x)

tievalsM :: [E] -> Scheme [L]
tievalsM = mapM alloc

-- |Scheme @call-with-current-continuation@
callcc :: [E] -> Scheme [E]
callcc =
  oneargM
    ( \e ->
        case e of
          Ef _ ->
            callCC $ \k -> do
              l <- alloc (Em Unspecified)
              applicateM e [Ef (l, k)]
          _ -> wrongM ("bad procedure argument to call/cc: " <> show e)
    )

-- |Scheme @values@
values :: [E] -> Scheme [E]
values = pure

-- |Scheme @call-with-values@
cwv :: [E] -> Scheme [E]
cwv = twoargM (\e1 e2 -> applicateM e1 [] >>= applicateM e2)

dropfirst :: [E] -> Int -> [E]
dropfirst es v = drop v es

takefirst :: [E] -> Int -> [E]
takefirst es v = take v es

-- |Evaluate an expression with the standard environment and store.
evalStd :: Expr -> A
evalStd prog = runSchemeWith stdEnv stdStore (evalM prog)

-- |The standard environment
stdEnv :: U
stdEnv = zip stdEnvNames [1 ..]

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
