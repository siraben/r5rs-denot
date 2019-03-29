{-# LANGUAGE LambdaCase #-}

import Data.List
import Data.Maybe

-- Locations
type L = Int

-- Natural numbers
newtype N =
  N Integer

-- Boolean
type T = Bool

-- Symbol
type Q = String

-- Characters
type H = Char

-- Numbers
type R = Integer

-- Constants
data Con
  = Symbol Q
  | Boolean T
  | Number R
  | Character H
  | Nil

instance Show Con where
  show (Symbol q) = q
  show (Character h) = "#\\" ++ [h]
  show (Number r) = show r
  show (Boolean True) = "#t"
  show (Boolean False) = "#t"
  show Nil = "()"

-- Expressed values
data E
  = Ek Con
  | Ep (L, L, T)
  | Ev ([L], T)
  | Es ([L], T)
  | Em M
  | Ef F

instance Show E where
  show (Ek con) = show con
  show (Ep (car, cdr, _)) = concat ["(", show car, " . ", show cdr, " )"]
  show (Ev (l, _)) = show l
  show (Es (l, _)) = show l
  show (Em m) = show m
  show (Ef f) = "#<procedure>"

-- Miscellaneous
data M
  = Boom T
  | Null
  | Undefined
  | Unspecified

instance Show M where
  show (Boom True) = "#t"
  show (Boom False) = "#f"
  show Null = "null"
  show Unspecified = "#<unspecified>"
  show Undefined = "#<undefined>"

-- Procedures
type F = (L, [E] -> K -> C)

-- Stores
type S = [(E, T)]

-- Environment
type U = [(Ide, L)]

-- Command continuation
type C = S -> A

-- Expression continuation
type K = [E] -> C

-- Answer
type A = String

-- Errors
newtype X a =
  X a

-- Identifier
type Ide = String

-- Expressions
data Expr
  = Const Con
  | Id Ide
  | App Expr
        [Expr]
  | Lambda [Ide]
           [Com]
           Expr
  | LambdaV [Ide]
            Ide
            [Com]
            Expr
  | LambdaVV Ide
             [Com]
             Expr
  | If Expr
       Expr
       Expr
  | IfPartial Expr
              Expr
  | Set Ide
        Expr

instance Show Expr where
  show (Const con) = show con
  show (Id ide) = ide
  show (App e1 e2) = concat ["(", show e1, " ", show e2, ")"]
  show (Lambda l c e) =
    concat ["(lambda ", show l, " ", show c, " ", show e, ") "]
  show (LambdaV l i c e) =
    concat ["(lambda ", show l, " (", i, ") ", show c, " ", show e, ") "]
  show (LambdaVV i c e) = concat ["(lambda ", i, " ", show c, " ", show e, ") "]
  show (If p c a) =
    concat ["(if ", show p, " then ", show c, " else ", show a, ") "]
  show (IfPartial p c) = concat ["(if ", show p, " then ", show c, ") "]
  show (Set i e) = concat ["(set! ", i, " ", show e]

-- Commands
type Com = Expr

eval :: Expr -> U -> K -> C
eval (Const a) p k = send (Ek a) k
eval (Id i) p k =
  hold
    (envLookup p i)
    (single
       (\case
          Em Undefined -> wrong ("Undefined variable: " ++ i ++ " " ++ show p)
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
-- twoarg
--   (\e1 e2 k s ->
--      (\s' -> send (Ep (new s, new s', True)) k (update (new s') e2 s'))
--        (update (new s) e1 s))
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
evalc [] p t = t
evalc (g0:gs) p t = eval g0 p $ \es -> evalc gs p t

envLookup :: U -> Ide -> L
envLookup [] _ = -1
envLookup ((a, b):as) p
  | p == a = b
  | otherwise = envLookup as p

extends :: U -> [Ide] -> [L] -> U
extends p [] _ = p
extends p (i:is) (a:as) = extends ((i, a) : p) is as

send :: E -> K -> C
send e k = k [e]

wrong :: String -> C
wrong a p = "Error: " ++ a ++ "\nStore: " ++ show p

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
new (_:l) = 1 +
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

-- Generate a store of size n.
genStore :: Int -> S
genStore n = replicate n (Em Undefined, False)

replace :: Int -> a -> [a] -> [a]
replace 0 x (_:as) = x : as
replace n x (a:as) = a : replace (n - 1) x as

update :: L -> E -> S -> S
update l e = replace l (e, True)

assign :: L -> E -> C -> C
assign a e t s = t $ update a e s

truish :: E -> T
truish (Ek (Boolean False)) = False
truish (Ek (Boolean True)) = True

permute :: [Expr] -> [Expr]
permute = id

unpermute :: [E] -> [E]
unpermute = id

applicate :: E -> [E] -> K -> C
applicate (Ef e) es k = (snd e) es k
applicate _ _ _ = wrong "bad procedure"

onearg :: (E -> K -> C) -> ([E] -> K -> C)
onearg x [e] k = x e k
onearg _ _ _ = wrong "wrong number of arguments"

twoarg :: (E -> E -> K -> C) -> [E] -> K -> C
twoarg x [e1, e2] k = x e1 e2 k
twoarg _ _ _ = wrong "wrong number of arguments"

list :: [E] -> K -> C
list [] k = send (Ek Nil) k
list (x:xs) k = list xs $ single $ \e -> cons [x, e] k

cons :: [E] -> K -> C
cons =
  twoarg
    (\e1 e2 k s ->
       (\s' -> send (Ep (new s, new s', True)) k (update (new s') e2 s'))
         (update (new s) e1 s))

add :: [E] -> K -> C
add =
  twoarg
    (\e1 e2 k ->
       case e1 of
         (Ek (Number r1)) ->
           case e2 of
             (Ek (Number r2)) -> send (Ek (Number (r1 + r2))) k
             _ -> wrong "non-numeric argument to +"
         _ -> wrong "non-numeric argument to +")

mult :: [E] -> K -> C
mult =
  twoarg
    (\e1 e2 k ->
       case e1 of
         (Ek (Number r1)) ->
           case e2 of
             (Ek (Number r2)) -> send (Ek (Number (r1 * r2))) k
             _ -> wrong "non-numeric argument to *"
         _ -> wrong "non-numeric argument to *")

sub :: [E] -> K -> C
sub =
  twoarg
    (\e1 e2 k ->
       case e1 of
         (Ek (Number r1)) ->
           case e2 of
             (Ek (Number r2)) -> send (Ek (Number (r1 - r2))) k
             _ -> wrong "non-numeric argument to -"
         _ -> wrong "non-numeric argument to -")

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

apply =
  twoarg
    (\e1 e2 k ->
       case e1 of
         Ef f -> valueslist [e2] (\es -> applicate e1 es k)
         _ -> wrong "bad procedure argument to apply")

valueslist :: [E] -> K -> C
valueslist =
  onearg
    (\e k ->
       case e of
         Ep _ ->
           cdr
             [e]
             (\es ->
                valueslist es (\es -> car [e] (single (\e -> k (e : es)))))
         (Ek Nil) -> k []
         _ -> wrong "non-list argument to values-list")

tievals :: ([L] -> C) -> [E] -> C
tievals f [] s = f [] s
tievals f (e:es) s = tievals (\as -> f (new s : as)) es (update (new s) e s)

tievalsrest :: ([L] -> C) -> Int -> [E] -> C
tievalsrest f es v =
  list (dropfirst es v) (single (\e -> tievals f (takefirst es v ++ [e])))

dropfirst = drop

takefirst = take

idKCont :: [E] -> S -> A
idKCont e s = concat ["Result: ", show e, "\nStore: ", show s]

sId = Lambda ["x"] [] (Id "x")

sFst = Lambda ["x", "y"] [] (Id "x")

sSnd = Lambda ["x", "y"] [] (Id "y")

-- Curried first and second.
scFst = Lambda ["x"] [] (Lambda ["y"] [] (Id "x"))

scSnd = Lambda ["x"] [] (Lambda ["y"] [] (Id "y"))

-- Passes: returns 3
idTest = App sId [Const (Number 3)]

-- Fails: returns 5 
fstTest = App sFst [Const (Number 3), Const (Number 5)]

-- Passes: returns 5
sndTest = App sSnd [Const (Number 3), Const (Number 5)]

sFstTest = App (App scFst [Const (Number 3)]) [Const (Number 5)]

sSndTest = App (App scSnd [Const (Number 3)]) [Const (Number 5)]


addTest = (App (Id "add") [Const (Number 3), Const (Number 5)])
evalWithStore prog n = eval prog emptyEnv idKCont (genStore n)

evalStd prog = putStrLn $ eval prog stdEnv idKCont stdStore
evalr prog = evalWithStore prog 10

stdEnv = [("add", 3)]

stdStore = [(Em Undefined, False),
            (Em Undefined, False),
            (Em Undefined, False),
            (Ef (1, add), True)] ++ (genStore 10)

--            (Id "x", (Ek (Number 3)))
--           ] ++ (genStore 10)

addTest2 = App (Lambda ["x"] [] (App (Id "add") [Id "x", Id "x"]))
               [Const (Number 10)]
