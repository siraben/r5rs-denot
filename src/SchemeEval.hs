{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures -fdefer-typed-holes -fno-warn-unused-imports -fdefer-type-errors #-}

module SchemeEval where

import Data.Maybe
import SchemeParser
import SchemeTypes
import qualified Data.IntMap as M
import Control.Monad.Reader
import Control.Monad.Cont
import Control.Monad.State
import Control.Monad.Identity
import Data.Function

{-
eval :: Expr -> U -> K -> C
     = Expr -> U -> ([E] -> C) -> C
     = Expr -> U -> ([E] -> S -> A) -> S -> A
     ~ Expr -> U -> ([E] -> S -> Identity A) -> S -> Identity A
     ~ Expr -> U -> (StateT S (ContT A Identity)) [E]
     ~ Expr -> ReaderT U (StateT S (ContT A Identity)) [E]
-}

eval1 :: Expr -> U -> ([E] -> C) -> C
eval2 :: Expr -> U -> ([E] -> S -> A) -> S -> A
eval3 :: Expr -> U -> ([E] -> S -> Identity A) -> S -> Identity A
eval4 :: Expr -> U -> (StateT S (ContT A Identity)) [E]
eval5 :: Expr -> ReaderT U (StateT S (ContT A Identity)) [E]

eval1 = eval

eval2 = eval1

eval3 e u k s = Identity (eval2 e u (\es s -> runIdentity (k es s)) s)

eval4 e u = StateT (\s -> ContT (\k -> eval3 e u (curry k) s))

eval5 e = ReaderT (eval4 e)

eval6 e = Scheme (eval5 e)

-- Combine into one expression
reflect :: forall u r s a. (u -> (a -> s -> r) -> s -> r) -> Scheme Maybe u r s a
reflect f = Scheme (ReaderT (\u -> StateT (ContT . g u)))
  where
    g u s k = Just (f u (\a s -> fromJust (curry k a s)) s)

reflect' :: Monad m => forall u r s a. (u -> (a -> s -> m r) -> s -> m r) -> Scheme m u r s a
reflect' f = Scheme (ReaderT (\u -> StateT (ContT . g u)))
  where
    g u s k = f u (curry k) s

reify :: Scheme Maybe u r s a -> u -> (a -> s -> r) -> s -> r
reify f r k s = f
              & unScheme
              & (`runReaderT` r)
              & (`runStateT` s)
              & (`runContT` (\(a,s) -> Just (k a s)))
              & fromJust

reify' :: Monad m => Scheme m u r s a -> u -> (a -> s -> m r) -> s -> m r
reify' f r k s = f
              & unScheme
              & (`runReaderT` r)
              & (`runStateT` s)
              & (`runContT` uncurry k)

runScheme f = f
            & unScheme
            & (`runReaderT` stdEnv)
            & (`runStateT` emptyStore)
            & (`runContT` pure)

sputChar :: MonadIO m => Char -> Scheme m u r s ()
sputChar = liftIO . putChar

sputStrLn :: MonadIO m => String -> Scheme m u r s ()
sputStrLn = liftIO . putStrLn

{-
λ> reify . reflect
reify . reflect
  :: (u -> (a -> s -> r) -> s -> r) -> u -> (a -> s -> r) -> s -> r
λ> reflect . reify
reflect . reify :: Scheme Maybe u r s a -> Scheme Maybe u r s a
λ> reify' . reflect'
reify' . reflect'
  :: Monad m =>
     (u -> (a -> s -> m r) -> s -> m r)
     -> u -> (a -> s -> m r) -> s -> m r
λ> reflect' . reify'
reflect' . reify'
  :: Monad m => Scheme m u r s a -> Scheme m u r s a
-}

evalM :: Expr -> Scheme' [E]
evalM (Const a) =
  sendM (Ek a)
evalM (Id i) = do
  ρ <- ask
  ε <- singleM =<< holdM (envLookup ρ i)
  case ε of
    Em Undefined -> wrongM ("Undefined variable: " <> i)
    ε' -> sendM ε'
evalM (App e0 es) = do
  (ε:εs) <- evalsM (e0 : es)
  applicateM ε εs
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
evalM (Lambda is γ e0) = do
  σ <- get
  ρ <- ask
  let α = new σ
  sendM (Ef (α, ϕ ρ))
  where
    ϕ ρ = \εs κ' ->
      if length εs == length is
        then
          tievals
            ((\ρ' -> evalc γ ρ' (eval e0 ρ' κ')) . extends ρ is)
            εs
        else
          wrong
            ( "wrong number of arguments, expected "
                <> show (length is)
                <> ", namely "
                <> show is
                <> " but got "
                <> show (length εs)
                <> " instead"
            )
evalM (LambdaV is i gs e0) = do
  σ <- get
  ρ <- ask
  let α = new σ
  sendM (Ef (α, ϕ ρ))
  where
    ϕ ρ = \εs κ' ->
      if length εs >= length is
        then tievalsrest
               ((\ρ' -> evalc gs ρ' (eval e0 ρ' κ')) . extends ρ (is <> [i]))
               (length is)
               εs
        else wrong
               ("too few arguments, expected at least " <>
                show (length is) <> ", namely " <> show is)
evalM (LambdaVV i gs e0) = evalM (LambdaV [] i gs e0)
evalM (Set i e) = do
  [ε] <- evalM e
  ρ <- ask
  modify (update (envLookup ρ i) ε)
  sendM (Em Unspecified)

eval :: Expr -> U -> K -> C
eval e = reify (evalM e)


-- |Evaluate a list of expressions, sending the collected result to
-- the continuation.
evals :: [Expr] -> U -> K -> C
evals = reify . evalsM

-- |Evaluate a list of expressions, sending the collected result to
-- the continuation.
evalsM :: [Expr] -> Scheme' [E]
evalsM = mapM (singleM <=< evalM)

-- |Evaluate a list of commands, returning to the continuation.
evalc :: [Expr] -> U -> C -> C
evalc [] ρ θ      = θ
evalc (g0:gs) ρ θ = eval g0 ρ $ \es -> evalc gs ρ θ
-- evalc γ ρ = reify (evalcM γ ρ) ρ

-- untested
evalcM :: [Expr] -> U -> Scheme' ()
evalcM γ ρ = mapM_ (\ε -> local (const ρ) (evalM ε)) γ

-- |Look up an identifier in the environment.
envLookup :: U -> Ide -> L
envLookup u i = fromMaybe 0 (lookup i u)

-- |Extend an environment with a list of identifiers and their store
-- locations.
extends :: U -> [Ide] -> [L] -> U
extends ρ is αs = zip is αs <> ρ

-- |Send a value to the continuation.
send :: E -> K -> C
send ε κ = κ [ε]

sendM e = pure [e]

-- |Raise an error.
wrong :: X -> C
wrong χ ρ = error χ

-- wrongM :: MonadFail m => String -> m a
wrongM s = error s

-- |Given a location, look it up in the store and send it to the
-- continuation.
hold :: L -> K -> C
hold α κ σ@(c, m) = send (fst (m M.! α)) κ σ

holdM :: L -> Scheme' [E]
holdM a = do
  (c,m) <- get
  sendM (fst (m M.! a))

single :: (E -> C) -> K
single ϕ es
  | length es == 1 = ϕ (es !! 0)
  | otherwise =
    wrong
      ("wrong number of return values, expected 1 but got " <> show (length es))

singleM es =
  if length es == 1
    then pure (head es)
    else wrongM ("wrong number of return values, expected 1 but got " <> show (length es))

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

assign :: L -> E -> C -> C
assign α ε θ σ = θ (update α ε σ)

truish :: E -> T
truish (Ek (Boolean False)) = False
truish _                    = True

-- |Permute an expression list (as the order of evaluation of
-- arguments is undefined in Scheme).  Must be an inverse operation to
-- @unpermute@.
permute :: [Expr] -> [Expr]
permute = id

-- |Unpermute a value list (as the order of evaluation of arguments is
-- undefined in Scheme).  Must be an inverse operation to @permute@.
unpermute :: [E] -> [E]
unpermute = id

-- |Apply a Scheme procedure to a Haskell function that accepts list
-- of values, passing them as operands to the procedure.
applicate :: E -> [E] -> K -> C
applicate (Ef ε) εs κ = snd ε εs κ
applicate χ _ _ =
  wrong ("failed to apply " <> show χ <> ", expected a procedure")

applicateM f es = reflect (const (applicate f es))

-- |Lift a Haskell function that takes one argument into a
-- Scheme procedure.
onearg :: (E -> K -> C) -> [E] -> K -> C
onearg ζ [ε] κ = ζ ε κ
onearg _ a _ =
  wrong ("wrong number of arguments, expected 1 but got " <> show (length a))

oneargM z [e] = z =<< e
oneargM _ a =
  wrongM ("wrong number of arguments, expected 1 but got " <> show (length a))

-- |Lift a Haskell function that takes two arguments into a Scheme
-- procedure.
twoarg :: (E -> E -> K -> C) -> [E] -> K -> C
twoarg ζ [ε1, ε2] κ = ζ ε1 ε2 κ
twoarg _ χ _ =
  wrong
    ("wrong number of arguments, expected 2 but got " <>
     show (length χ) <> ": " <> show χ)

-- |Scheme @list@, also an example of how Scheme procedures can be
-- defined from other ones, but written in CPS.
list :: [E] -> K -> C
list [] κ     = send (Ek Nil) κ
list (e:es) κ = list es $ single $ \εs -> cons [e, εs] κ
-- TODO: rewrite with mapM

-- |Scheme @cons@.
cons :: [E] -> K -> C
cons =
  twoarg
    (\ε1 ε2 κ s ->
       (\s' -> send (Ep (new s, new s', True)) κ (update (new s') ε2 s'))
         (update (new s) ε1 s))

factorial :: [E] -> K -> C
factorial =
  onearg
    (\ε1 κ ->
       case ε1 of
         (Ek (Number 0)) -> send (Ek (Number 1)) κ
         m@(Ek (Number n)) ->
           factorial [Ek (Number (n - 1))] $ single $ \e -> mult [e, m] κ
         χ -> wrong ("non-numeric argument to factorial" <> show χ))

makeNumBinop name constructor op =
  twoarg
    (\ε1 ε2 κ ->
       case ε1 of
         (Ek (Number r1)) ->
           case ε2 of
             (Ek (Number r2)) -> send (constructor (op r1 r2)) κ
             χ ->
               wrong
                 ("non-numeric argument to " <>
                  name <> ", got " <> show χ <> " instead")
         χ ->
           wrong
             ("non-numeric argument to " <>
              name <> ", got " <> show χ <> " instead"))

-- |Scheme @+@
add :: [E] -> K -> C
add = makeNumBinop "+" (Ek . Number) (+)

-- |Scheme @<@
less :: [E] -> K -> C
less = makeNumBinop "<" (Ek . Boolean) (<)

-- |Scheme @>@
more :: [E] -> K -> C
more = makeNumBinop ">" (Ek . Boolean) (>)

-- |Scheme @=@
eqli :: [E] -> K -> C
eqli = makeNumBinop "=" (Ek . Boolean) (==)

-- |Scheme @>=@
eqlig :: [E] -> K -> C
eqlig = makeNumBinop ">=" (Ek . Boolean) (>=)

-- |Scheme @<=@
eqlilt :: [E] -> K -> C
eqlilt = makeNumBinop "<=" (Ek . Boolean) (<=)

-- |Scheme @*@
mult :: [E] -> K -> C
mult = makeNumBinop "*" (Ek . Number) (*)

-- |Scheme @-@
sub :: [E] -> K -> C
sub = makeNumBinop "-" (Ek . Number) (-)

-- |Scheme @modulo@
smod :: [E] -> K -> C
smod = makeNumBinop "modulo" (Ek . Number) mod

-- |Scheme @div@
sdiv :: [E] -> K -> C
sdiv = makeNumBinop "div" (Ek . Number) div

-- |Scheme @car@
car :: [E] -> K -> C
car = reify' (Scheme (ReaderT (\u -> StateT (ContT . g u))))
  where
    g u s k = car' u (\a s -> (curry k a s)) s
car' =
  onearg
    (\case
       (Ep (a, _, _)) -> hold a
       χ -> \_ -> wrong ("non-pair argument to car: " <> show χ))

-- |Scheme @cdr@
cdr :: [E] -> K -> C
cdr =
  onearg
    (\case
       (Ep (_, a, _)) -> hold a
       χ -> \_ -> wrong ("non-pair argument to cdr: " <> show χ))

-- |Scheme @set-car!@
setcar :: [E] -> K -> C
setcar =
  twoarg
    (\ε1 ε2 κ ->
       case ε1 of
         Ep (a, _, True) -> assign a ε2 (send (Em Unspecified) κ)
         Ep _ -> wrong "immutable argument to set-car!"
         χ -> wrong ("non-pair argument to set-cdr!: " <> show χ))

-- |Scheme @set-car@
setcdr :: [E] -> K -> C
setcdr =
  twoarg
    (\ε1 ε2 κ ->
       case ε1 of
         Ep (_, a, True) -> assign a ε2 (send (Em Unspecified) κ)
         Ep _ -> wrong "immutable argument to set-cdr!"
         χ -> wrong ("non-pair argument to set-cdr! got " <> show χ))

-- |Scheme @eqv?@
eqv :: [E] -> K -> C
eqv =
  twoarg
    (\ε1 ε2 ->
       case (ε1, ε2) of
         (Ek α, Ek β)                 -> retbool $ α == β
         (Em α, Em β)                 -> retbool $ α == β
         (Ev α, Ev β)                 -> retbool $ α == β
         (Ep (α, x, _), Ep (β, y, _)) -> retbool $ α == β && x == y
         (Ef (α, _), Ef (β, _))       -> retbool $ α == β
         _                            -> retbool False)

retbool :: Bool -> K -> C
retbool = send . Ek . Boolean

predLift :: (E -> Bool) -> [E] -> K -> C
predLift p = onearg (retbool . p)

-- |Scheme @number?@
numberp :: [E] -> K -> C
numberp = predLift p
  where
    p (Ek (Number _)) = True
    p _               = False

-- |Scheme @boolean?@
booleanp :: [E] -> K -> C
booleanp = predLift p
  where
    p (Ek (Boolean _)) = True
    p _                = False

-- |Scheme @symbol?@
symbolp :: [E] -> K -> C
symbolp = predLift p
  where
    p (Ek (Symbol _)) = True
    p _               = False

-- |Scheme @procedure?@
procedurep :: [E] -> K -> C
procedurep = predLift p
  where
    p (Ef _) = True
    p _      = False

-- |Scheme @pair?@
pairp :: [E] -> K -> C
pairp = predLift p
  where
    p (Ep _) = True
    p _      = False

-- |Scheme @null?@
nullp :: [E] -> K -> C
nullp = predLift p
  where
    p (Ek Nil) = True
    p _        = False

-- |Scheme @string?@
stringp :: [E] -> K -> C
stringp = predLift p
  where
    p (Ek (String _)) = True
    p _        = False

-- |Scheme @symbol->string@
symbolToString :: [E] -> K -> C
symbolToString = onearg
  (\case
      (Ek (Symbol q)) -> send (Ek (String q))
      v -> \_ -> wrong ("non-symbol argument to symbol->string: " <> show v))

-- |Scheme @string->symbol@
stringToSymbol :: [E] -> K -> C
stringToSymbol = onearg
  (\case
      (Ek (String q)) -> send (Ek (Symbol q))
      v -> \_ -> wrong ("non-string argument to string->symbol: " <> show v))

-- |Scheme @string-append@
stringAppend = twoarg
 (\ε1 ε2 ->
    case (ε1, ε2) of
      (Ek (String p), Ek (String q)) -> send (Ek (String (p <> q)))
      (χ, Ek (String q)) -> \_ -> wrong
                                    ("non-string argument to string-append: " <> show χ)
      (Ek (String p), χ) -> \_ -> wrong
                                    ("non-string argument to string-append: " <> show χ)
      (χ, χ') -> \_ -> wrong ("non-string arguments to string-append: " <> show χ <> " " <> show χ'))

-- |Scheme @number->string
numberToString = onearg
  (\case
      (Ek (Number n)) -> send (Ek (String (show n)))
      χ -> \_ -> wrong ("non-numeric argument to number->string: " <> show χ))

liftExpr = applicate . head . fst . evalStd

liftString = liftExpr . rparse

-- |Parse and evaluate a string.
reval :: String -> A
reval s =
  case readProg s of
    Right res -> evalStd res
    Left err  -> error ("Parse error: " <> show err)

-- |Parse a string into an expression.
rparse :: String -> Expr
rparse s =
  case readProg s of
    Right res -> res
    Left err    -> error ("Parse error: " <> show err)

-- |An example of defining a Scheme procedure given an expression.
recursive =
  liftExpr
    (Lambda
       ["fn"]
       []
       (App
          (Lambda ["h"] [] (App (Id "h") [Id "h"]))
          [ Lambda
              ["g"]
              []
              (App
                 (Id "fn")
                 [ LambdaVV
                     "arglist"
                     []
                     (App (Id "apply") [App (Id "g") [Id "g"], Id "arglist"])
                 ])
          ]))

-- |Scheme @apply@
apply :: [E] -> K -> C
apply =
  twoarg
    (\ε1 ε2 κ ->
       case ε1 of
         Ef f -> valueslist [ε2] (\εs -> applicate ε1 εs κ)
         χ    -> wrong ("bad procedure argument to apply: " <> show χ))

valueslist :: [E] -> K -> C
valueslist =
  onearg
    (\ε κ ->
       case ε of
         Ep _ ->
           cdr
             [ε]
             (\εs -> valueslist εs (\εs -> car [ε] (single (\ε -> κ (ε : εs)))))
         (Ek Nil) -> κ []
         χ -> wrong ("non-list argument to values-list:" <> show χ))

tievals :: ([L] -> C) -> [E] -> C
tievals ϕ [] σ     = ϕ [] σ
tievals ϕ (ε:εs) σ = tievals (\αs -> ϕ (new σ : αs)) εs (update (new σ) ε σ)

-- tievals :: ([L] -> S -> A) -> [E] -> S -> A
tievalsM f l s = reflect' (\_ _ s -> tievals f l s)
-- tievalsM f l s = do
--   newLocs <- traverse (\e -> update <$> gets new <*> pure e) l

--   -- forM_ l (\e -> do
--   --             l <- gets new
--   --             modify (update l e)
--   --             )
--   pure ()

-- |Scheme @call-with-current-continuation@
callcc :: [E] -> K -> C
callcc =
  onearg
    (\ε κ ->
       case ε of
         Ef _ ->
           \σ ->
             applicate
               ε
               [Ef (new σ, \εs κ' -> κ εs)]
               κ
               (update (new σ) (Em Unspecified) σ)
         _ -> wrong ("bad procedure argument to call/cc: " <> show ε))

-- |Scheme @values@
values :: [E] -> K -> C
values εs κ = κ εs

-- |Scheme @call-with-values@
cwv = twoarg (\ε1 ε2 κ -> applicate ε1 [] (\εs -> applicate ε2 εs κ))

tievalsrest :: ([L] -> C) -> Int -> [E] -> C
tievalsrest f es v =
  list (dropfirst es v) (single (\e -> tievals f (takefirst es v <> [e])))

dropfirst = drop

takefirst = take

-- |The "normal" continuation.
idKCont :: [E] -> S -> A
idKCont εs σ = (εs, σ)

-- |Evaluate an expression with the standard environment and store.
evalStd :: Expr -> A
evalStd prog = reify' (reflect' (eval prog)) stdEnv idKCont stdStore

-- |The standard environment
stdEnv :: U
stdEnv = zip stdEnvNames [1 ..]

exprDefinedOps :: [(String, [E] -> K -> C)]
exprDefinedOps = [("recursive", recursive)]

-- |The list of built-in operations.
builtInOps :: [(String, [E] -> K -> C)]
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
  ] <>
  exprDefinedOps

-- |The list of names of standard operations.
stdEnvNames :: [String]
stdEnvNames = map fst builtInOps

-- |The list of standard operations.
stdOps :: [[E] -> K -> C]
stdOps = map snd builtInOps

-- |The standard prelude.
stdPrelude :: S
stdPrelude = (n, M.fromList ((0,(Em Undefined, False)) : zipWith makeOpStore [1 ..] stdOps))
  where
    n = length stdOps + 1
    makeOpStore loc op = (loc, (Ef (loc, op), True))

-- |The standard store, consisting of a Prelude and infinite space.
stdStore :: S
stdStore = stdPrelude 
