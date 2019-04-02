{-# LANGUAGE LambdaCase #-}
module SchemeEval where
import SchemeTypes
import           Data.List
import           Data.Maybe

eval :: Expr -> U -> K -> C
eval (Const a) p k = send (Ek a) k
eval (Id i) p k =
  hold
    (envLookup p i)
    (single
       (\case
          Em Undefined -> wrong ("Undefined variable: " ++ i)
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
eval (Lambda is gs e0) p k =
  \s ->
    send
      (Ef
         ( new s
         , \es k' ->
             if length es == length is
               then tievals
                      ((\p' -> evalc gs p' (eval e0 p' k')) . extends p is)
                      es
               else wrong "wrong number of arguments"))
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
                       extends p (is ++ [i]))
                      (length is)
                      es
               else wrong "too few arguments"))
      k
      (update (new s) (Em Unspecified) s)
eval (LambdaVV i gs e0) p k = eval (LambdaV [] i gs e0) p k
eval (Set i e) p k =
  eval e p $ single $ \e -> assign (envLookup p i) e (send (Em Unspecified) k)

evals :: [Expr] -> U -> K -> C
evals [] _ k = k []
evals (e0:es) p k = eval e0 p $ single $ \e0 -> evals es p $ \es -> k (e0 : es)

evalc :: [Expr] -> U -> C -> C
evalc [] p t      = t
evalc (g0:gs) p t = eval g0 p $ \es -> evalc gs p t

envLookup :: U -> Ide -> L
envLookup [] _ = 0
envLookup ((a, b):as) p
  | p == a = b
  | otherwise = envLookup as p

extends :: U -> [Ide] -> [L] -> U
extends p [] _          = p
extends p (i:is) (a:as) = extends ((i, a) : p) is as

send :: E -> K -> C
send e k = k [e]

wrong :: String -> C
wrong a p = (a, Nothing, p)

hold :: L -> K -> C
hold a k s = send (fst (s !! a)) k s

single :: (E -> C) -> K
single p es
  | length es == 1 = p $ head es
  | otherwise = wrong "wrong number of return values"

-- new :: S -> Either String L
-- new [] = Left "empty store"
-- new l = case findIndex ((\case
--   Em Undefined -> True
--   _ -> False) . fst) l of
--           Just a  -> Right a
--           Nothing -> Left "out of memory"
new :: S -> L
new [] = error "empty store"
-- Because lists are 1-indexed, we ignore the first element.
new (_:l) =
  1 +
  fromMaybe
    (error "out of memory")
    (findIndex
       ((\case
           Em Undefined -> True
           _ -> False) .
        fst)
       l)

emptyEnv :: U
emptyEnv = []

emptyStore :: S
emptyStore = []

replace :: Int -> a -> [a] -> [a]
replace 0 x (_:as) = x : as
replace n x (a:as) = a : replace (n - 1) x as

update :: L -> E -> S -> S
update l e = replace l (e, True)

assign :: L -> E -> C -> C
assign a e t s = t $ update a e s

truish :: E -> T
truish (Ek (Boolean False)) = False
truish (Ek (Boolean True))  = True

permute :: [Expr] -> [Expr]
permute = id

unpermute :: [E] -> [E]
unpermute = id

applicate :: E -> [E] -> K -> C
applicate (Ef e) es k = snd e es k
applicate _ _ _       = wrong "bad procedure"

onearg :: (E -> K -> C) -> ([E] -> K -> C)
onearg x [e] k = x e k
onearg _ _ _   = wrong "wrong number of arguments"

twoarg :: (E -> E -> K -> C) -> [E] -> K -> C
twoarg x [e1, e2] k = x e1 e2 k
twoarg _ _ _        = wrong "wrong number of arguments"

list :: [E] -> K -> C
list [] k     = send (Ek Nil) k
list (x:xs) k = list xs $ single $ \e -> cons [x, e] k

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
         _ -> wrong "non-numeric argument to factorial")

makeNumBinop name constructor op =
  twoarg
    (\e1 e2 k ->
       case e1 of
         (Ek (Number r1)) ->
           case e2 of
             (Ek (Number r2)) -> send (constructor (op r1 r2)) k
             _                -> wrong ("non-numeric argument to " ++ name)
         _ -> wrong ("non-numeric argument to " ++ name))
    
add :: [E] -> K -> C
add = makeNumBinop "+" (Ek . Number) (+)

less :: [E] -> K -> C
less = makeNumBinop "<" (Ek . Boolean) (<)

more :: [E] -> K -> C
more = makeNumBinop ">" (Ek . Boolean) (>)

eqli :: [E] -> K -> C
eqli = makeNumBinop "=" (Ek . Boolean) (==)

eqlig :: [E] -> K -> C
eqlig = makeNumBinop ">=" (Ek . Boolean) (>=)

eqlilt :: [E] -> K -> C
eqlilt = makeNumBinop "<=" (Ek . Boolean) (<=)
        
mult :: [E] -> K -> C
mult = makeNumBinop "*" (Ek . Number) (*)

sub :: [E] -> K -> C
sub = makeNumBinop "-" (Ek . Number) (-)

smod :: [E] -> K -> C
smod = makeNumBinop "modulo" (Ek . Number) (mod)

sdiv :: [E] -> K -> C
sdiv = makeNumBinop "div" (Ek . Number) (div)

car :: [E] -> K -> C
car =
  onearg
    (\case
       (Ep (a, _, _)) -> hold a
       _ -> \_ -> wrong "non-pair argument to car")

cdr :: [E] -> K -> C
cdr =
  onearg
    (\case
       (Ep (_, a, _)) -> hold a
       _ -> \_ -> wrong "non-pair argument to cdr")

setcar :: [E] -> K -> C
setcar =
  twoarg
    (\e1 e2 k ->
       case e1 of
         Ep (a, _, True) -> assign a e2 (send (Em Unspecified) k)
         Ep _            -> wrong "immutable argument to set-car!"
         _               -> wrong "non-pair argument to set-car!")

eqv :: [E] -> K -> C
eqv =
  twoarg
    (\e1 e2 ->
       case (e1, e2) of
         (Ek a, Ek b)                 -> retbool (a == b)
         (Em a, Em b)                 -> retbool (a == b)
         (Ev a, Ev b)                 -> retbool (a == b)
         (Ep (a, x, _), Ep (b, y, _)) -> retbool ((a == b) && (x == y))
         (Ef (a, _), Ef (b, _))       -> retbool (a == b)
         _                            -> retbool False)
  where
    retbool :: Bool -> K -> C
    retbool b = send (Ek (Boolean b))

apply :: [E] -> K -> C
apply =
  twoarg
    (\e1 e2 k ->
       case e1 of
         Ef f -> valueslist [e2] (\es -> applicate e1 es k)
         _    -> wrong "bad procedure argument to apply")

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
         _ -> wrong "non-list argument to values-list")

tievals :: ([L] -> C) -> [E] -> C
tievals f [] s     = f [] s
tievals f (e:es) s = tievals (\as -> f (new s : as)) es (update (new s) e s)

-- Call with current continuation
cwcc :: [E] -> K -> C
cwcc =
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
         _ -> wrong "bad procedure argument")

values :: [E] -> K -> C
values es k = k es

-- |Call with values
cwv = twoarg (\e1 e2 k -> applicate e1 [] (\es -> applicate e2 es k))

tievalsrest :: ([L] -> C) -> Int -> [E] -> C
tievalsrest f es v =
  list (dropfirst es v) (single (\e -> tievals f (takefirst es v ++ [e])))

dropfirst = drop
takefirst = take

-- |The "normal" continuation.
idKCont :: [E] -> S -> A
idKCont e s = ("", Just e, take (new s) s)

-- |Evaluate an expression with the standard environment and store.
evalStd prog = eval prog stdEnv idKCont stdStore

-- |The standard environment
stdEnv :: U
stdEnv = zip stdEnvNames [1..]

-- |The list of built-in ops.
builtInOps = [("+", add),
              ("*", mult),
              ("-", sub),
              ("/", sdiv),
              ("modulo", smod),
              ("<", less),
              (">", more),
              ("=", eqli),
              (">=", eqlig),
              ("<=", eqlilt),
              ("cons", cons),
              ("car", car),
              ("cdr", cdr),
              ("list", list),
              ("eqv?", eqv),
              ("set-car!", setcar),
              ("apply", apply),
              ("call-with-values", cwv),
              ("call-with-current-continuation", cwcc),
              ("call/cc", cwcc)
             ]

-- |The list of names of standard operations.
stdEnvNames :: [String]
stdEnvNames = map fst builtInOps

-- |The list of standard operations.
stdOps :: [[E] -> K -> C]
stdOps = map snd builtInOps

-- |The standard prelude.
stdPrelude :: S
stdPrelude = [(Em Undefined, False)] ++ zipWith makeOpStore [1..] stdOps
  where
    makeOpStore loc op = (Ef (loc, op), True)

-- |The standard store, consisting of a Prelude and infinite space.
stdStore :: S
stdStore = stdPrelude ++ infStore
  where
    infStore = repeat (Em Undefined, False)
