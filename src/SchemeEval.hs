{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module SchemeEval where

import Data.Maybe
import SchemeParser
import SchemeTypes
import qualified Data.IntMap as M
import Control.Monad.Reader
import Control.Monad.Cont
import Control.Monad.Trans.Maybe
import Control.Monad.State
import Data.Function

newtype Scheme u k s a = Scheme { unScheme :: ReaderT u (ContT k (MaybeT (State s))) a }
                 deriving (Functor, Applicative, Monad, MonadReader u, MonadCont)

type Scheme' a = Scheme U [E] S a
{-
eval :: Expr -> U -> K -> C
     = Expr -> U -> ([E] -> C) -> C
     = Expr -> U -> ([E] -> S -> A) -> S -> A
     = Expr -> U -> ([E] -> S -> (Maybe [E], S)) -> S -> (Maybe [E], S)
     ~ Expr -> U -> ([E] -> MaybeT (State S) [E]) -> MaybeT (State S) [E]
     ~ Expr -> U -> ContT [E] (MaybeT (State S)) [E]
     ~ Expr -> Reader U (ContT [E] (MaybeT (State S)) [E])
-}


-- _  :: Expr -> U -> K -> C
eval1 :: Expr -> U -> ([E] -> C) -> C
eval1 = eval
eval2 :: Expr -> U -> ([E] -> S -> A) -> S -> A
eval2 = eval1
eval2' :: Expr -> U -> ([E] -> S -> (Maybe [E], S)) -> S -> (Maybe [E], S)
eval2' = eval2
eval3 :: Expr -> U -> ([E] -> State S (Maybe [E])) -> State S (Maybe [E])
eval3 e u k = state (eval2 e u (runState . k))
eval3' :: Expr -> U -> ([E] -> MaybeT (State S) [E]) -> MaybeT (State S) [E]
eval3' e u k = MaybeT (eval3 e u (runMaybeT . k))
eval4 :: Expr -> U -> ContT [E] (MaybeT (State S)) [E]
eval4 e u = ContT (eval3' e u)
eval5 :: Expr -> ReaderT U (ContT [E] (MaybeT (State S))) [E]
eval5 e = ReaderT (eval4 e)
eval6 :: Expr -> Scheme' [E]
eval6 = Scheme . eval5

-- Combine into one expression
reflect
  :: (u -> (a -> s -> (Maybe k, s)) -> s -> (Maybe k, s))
     -> Scheme u k s a
reflect act = Scheme (ReaderT (\u -> ContT (\k -> MaybeT (state (act u (runState . (runMaybeT . k)))))))

reify
  :: Scheme u k s a
     -> u -> (a -> s -> (Maybe k, s)) -> s -> (Maybe k, s)
reify f r k s = f
              & unScheme
              & (`runReaderT` r)
              & (`runContT` (MaybeT . state . k))
              & runMaybeT
              & (`runState` s)
{-
λ> reify . reflect
reify . reflect
  :: (u -> (a -> s -> (Maybe k, s)) -> s -> (Maybe k, s))
     -> u -> (a -> s -> (Maybe k, s)) -> s -> (Maybe k, s)
λ> reflect . reify
reflect . reify :: Scheme u k s a -> Scheme u k s a
-}

eval :: Expr -> U -> K -> C
eval (Const a) p k = send (Ek a) k
eval (Id i) p k =
  hold
    (envLookup p i)
    (single
       (\case
          Em Undefined -> wrong ("Undefined variable: " <> i)
          e -> send e k))
eval (App e0 e) p k =
  evals (permute (e0 : e)) p ((\(e:es) -> applicate e es k) . unpermute)
eval (If e0 e1 e2) p k =
  eval e0 p $
  single $ \e ->
    if truish e
      then eval e1 p k
      else eval e2 p k
eval (IfPartial e0 e1) p k =
  eval e0 p $
  single $ \e ->
    if truish e
      then eval e1 p k
      else send (Em Unspecified) k
eval (Lambda is γ e0) p k =
  \s ->
    send
      (Ef
         ( new s
         , \es k' ->
             if length es == length is
               then tievals
                      ((\p' -> evalc γ p' (eval e0 p' k')) . extends p is)
                      es
               else wrong
                      ("wrong number of arguments, expected " <>
                       show (length is) <>
                       ", namely " <>
                       show is <> " but got " <> show (length es) <> " instead")))
      k
      (update (new s) (Em Unspecified) s)
eval (LambdaV is i gs e0) p k =
  \s ->
    send
      (Ef
         ( new s
         , \es k' ->
             if length es >= length is
               then tievalsrest
                      ((\p' -> evalc gs p' (eval e0 p' k')) .
                       extends p (is <> [i]))
                      (length is)
                      es
               else wrong
                      ("too few arguments, expected at least " <>
                       show (length is) <> ", namely " <> show is)))
      k
      (update (new s) (Em Unspecified) s)
eval (LambdaVV i gs e0) p k = eval (LambdaV [] i gs e0) p k
eval (Set i e) p k =
  eval e p $ single $ \e -> assign (envLookup p i) e (send (Em Unspecified) k)

-- |Evaluate a list of expressions, sending the collected result to
-- the continuation.
evals :: [Expr] -> U -> K -> C
evals [] _ k = k []
evals (e0:es) p k = eval e0 p $ single $ \e0 -> evals es p $ \es -> k (e0 : es)

-- |Evaluate a list of commands, returning to the continuation.
evalc :: [Expr] -> U -> C -> C
evalc [] p θ      = θ
evalc (g0:gs) p θ = eval g0 p $ \es -> evalc gs p θ

-- |Look up an identifier in the environment.
envLookup :: U -> Ide -> L
envLookup u i = fromMaybe 0 (lookup i u)

-- |Extend an environment with a list of identifiers and their store
-- locations.
extends :: U -> [Ide] -> [L] -> U
extends p is as = zip is as <> p

-- |Send a value to the continuation.
send :: E -> K -> C
send e k = k [e]

-- |Raise an error.
wrong :: X -> C
wrong x p = (Nothing, p)

-- |Given a location, look it up in the store and send it to the
-- continuation.
hold :: L -> K -> C
hold a k s@(c, m) = send (fst (m M.! a)) k s

single :: (E -> C) -> K
single f es
  | length es == 1 = f (head es)
  | otherwise =
    wrong
      ("wrong number of return values, expected 1 but got " <> show (length es))

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

assign :: L -> E -> C -> C
assign a e θ s = θ (update a e s)

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
applicate (Ef e) es k = snd e es k
applicate x _ _ =
  wrong ("failed to apply " <> show x <> ", expected a procedure")

-- |Lift a Haskell function that takes one argument into a
-- Scheme procedure.
onearg :: (E -> K -> C) -> [E] -> K -> C
onearg ζ [e] k = ζ e k
onearg _ a _ =
  wrong ("wrong number of arguments, expected 1 but got " <> show (length a))

-- |Lift a Haskell function that takes two arguments into a Scheme
-- procedure.
twoarg :: (E -> E -> K -> C) -> [E] -> K -> C
twoarg ζ [e1, e2] k = ζ e1 e2 k
twoarg _ x _ =
  wrong
    ("wrong number of arguments, expected 2 but got " <>
     show (length x) <> ": " <> show x)

-- |Scheme @list@, also an example of how Scheme procedures can be
-- defined from other ones, but written in CPS.
list :: [E] -> K -> C
list [] k     = send (Ek Nil) k
list (e:es) k = list es $ single $ \es -> cons [e, es] k
-- TODO: rewrite with mapM

-- |Scheme @cons@.
cons :: [E] -> K -> C
cons =
  twoarg
    (\e1 e2 k s ->
       (\s' -> send (Ep (new s, new s', True)) k (update (new s') e2 s'))
         (update (new s) e1 s))

factorial :: [E] -> K -> C
factorial =
  onearg
    (\e1 k ->
       case e1 of
         (Ek (Number 0)) -> send (Ek (Number 1)) k
         m@(Ek (Number n)) ->
           factorial [Ek (Number (n - 1))] $ single $ \e -> mult [e, m] k
         x -> wrong ("non-numeric argument to factorial" <> show x))

makeNumBinop name constructor op =
  twoarg
    (\e1 e2 k ->
       case e1 of
         (Ek (Number r1)) ->
           case e2 of
             (Ek (Number r2)) -> send (constructor (op r1 r2)) k
             x ->
               wrong
                 ("non-numeric argument to " <>
                  name <> ", got " <> show x <> " instead")
         x ->
           wrong
             ("non-numeric argument to " <>
              name <> ", got " <> show x <> " instead"))

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
car =
  onearg
    (\case
       (Ep (a, _, _)) -> hold a
       x -> \_ -> wrong ("non-pair argument to car: " <> show x))

-- |Scheme @cdr@
cdr :: [E] -> K -> C
cdr =
  onearg
    (\case
       (Ep (_, a, _)) -> hold a
       x -> \_ -> wrong ("non-pair argument to cdr: " <> show x))

-- |Scheme @set-car!@
setcar :: [E] -> K -> C
setcar =
  twoarg
    (\e1 e2 k ->
       case e1 of
         Ep (a, _, True) -> assign a e2 (send (Em Unspecified) k)
         Ep _ -> wrong "immutable argument to set-car!"
         x -> wrong ("non-pair argument to set-cdr!: " <> show x))

-- |Scheme @set-car@
setcdr :: [E] -> K -> C
setcdr =
  twoarg
    (\e1 e2 k ->
       case e1 of
         Ep (_, a, True) -> assign a e2 (send (Em Unspecified) k)
         Ep _ -> wrong "immutable argument to set-cdr!"
         x -> wrong ("non-pair argument to set-cdr! got " <> show x))

-- |Scheme @eqv?@
eqv :: [E] -> K -> C
eqv =
  twoarg
    (\e1 e2 ->
       case (e1, e2) of
         (Ek a, Ek β)                 -> retbool $ a == β
         (Em a, Em β)                 -> retbool $ a == β
         (Ev a, Ev β)                 -> retbool $ a == β
         (Ep (a, x, _), Ep (β, y, _)) -> retbool $ a == β && x == y
         (Ef (a, _), Ef (β, _))       -> retbool $ a == β
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
 (\e1 e2 ->
    case (e1, e2) of
      (Ek (String p), Ek (String q)) -> send (Ek (String (p <> q)))
      (x, Ek (String q)) -> \_ -> wrong
                                    ("non-string argument to string-append: " <> show x)
      (Ek (String p), x) -> \_ -> wrong
                                    ("non-string argument to string-append: " <> show x)
      (x, x') -> \_ -> wrong ("non-string arguments to string-append: " <> show x <> " " <> show x'))

-- |Scheme @number->string
numberToString = onearg
  (\case
      (Ek (Number n)) -> send (Ek (String (show n)))
      x -> \_ -> wrong ("non-numeric argument to number->string: " <> show x))

valueStdExtract (Nothing, _) =
  error "Failed to extract value from expression"
valueStdExtract (Just a, _) = head a

liftExpr = applicate . valueStdExtract . evalStd

liftString = liftExpr . rparse

-- |Parse and evaluate a string.
reval :: String -> A
reval s =
  case readProg s of
    Right res -> evalStd res
    Left err  -> (Nothing, emptyStore)

-- |Parse a string into an expression.
rparse :: String -> Expr
rparse s =
  case readProg s of
    Right res -> res
    Left _    -> error ("Failed to parse" <> s)

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
    (\e1 e2 k ->
       case e1 of
         Ef f -> valueslist [e2] (\es -> applicate e1 es k)
         x    -> wrong ("bad procedure argument to apply: " <> show x))

valueslist :: [E] -> K -> C
valueslist =
  onearg
    (\e k ->
       case e of
         Ep _ ->
           cdr
             [e]
             (\es -> valueslist es (\es -> car [e] (single (\e -> k (e : es)))))
         (Ek Nil) -> k []
         x -> wrong ("non-list argument to values-list:" <> show x))

tievals :: ([L] -> C) -> [E] -> C
tievals f [] s     = f [] s
tievals f (e:es) s = tievals (\as -> f (new s : as)) es (update (new s) e s)

-- |Scheme @call-with-current-continuation@
callcc :: [E] -> K -> C
callcc =
  onearg
    (\e k ->
       case e of
         Ef _ ->
           \s ->
             applicate
               e
               [Ef (new s, \es k' -> k es)]
               k
               (update (new s) (Em Unspecified) s)
         _ -> wrong ("bad procedure argument to call/cc: " <> show e))

-- |Scheme @values@
values :: [E] -> K -> C
values es k = k es

-- |Scheme @call-with-values@
cwv = twoarg (\e1 e2 k -> applicate e1 [] (\es -> applicate e2 es k))

tievalsrest :: ([L] -> C) -> Int -> [E] -> C
tievalsrest f es v =
  list (dropfirst es v) (single (\e -> tievals f (takefirst es v <> [e])))

dropfirst = drop

takefirst = take

-- |The "normal" continuation.
idKCont :: [E] -> S -> A
idKCont e s = (Just e, s)

-- |Evaluate an expression with the standard environment and store.
evalStd prog = eval prog stdEnv idKCont stdStore

-- |The standard environment
stdEnv :: U
stdEnv = zip stdEnvNames [1 ..]

exprDefinedOps = [("recursive", recursive)]

-- |The list of built-in operations.
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
