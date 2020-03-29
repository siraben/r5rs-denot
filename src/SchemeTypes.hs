{-|
Module      : SchemeTypes
Description : Datatypes of r5rs-denot.

As defined in the R5RS standard.
-}
module SchemeTypes where

import Data.List
import qualified Data.IntMap as M

-- |Locations
type L = Int

-- |Natural numbers
newtype N =
  N Integer

-- |Boolean
type T = Bool

-- |Symbol
type Q = String

-- |Characters
type H = Char

-- |Numbers
type R = Integer

-- |Constants
data Con
  = Symbol Q
  | Boolean T
  | Number R
  | Character H
  | Nil
  deriving (Eq)

instance Show Con where
  show (Symbol q) = q
  show (Character h) = "#\\" ++ [h]
  show (Number r) = show r
  show (Boolean True) = "#t"
  show (Boolean False) = "#f"
  show Nil = "()"

-- |Expressed values
data E
  = Ek Con
  | Ep (L, L, T) -- pair
  | Ev ([L], T) -- vectors
  | Es ([L], T) -- strings
  | Em M
  | Ef F

instance Show E where
  show (Ek con) = show con
  show (Ep (car, cdr, _)) = concat ["~(", show car, " . ", show cdr, ")"]
  show (Ev (l, _)) = show l
  show (Es (l, _)) = show l
  show (Em m) = show m
  show (Ef f) = "#<procedure>"

-- |Show an expression, but in full (i.e. follow recursively go down
-- the @car@ and @cdr@ of the value in the given store.
showFull :: E -> S -> String
showFull l s = show' l
  where
    show' e@(Ep _) = "(" ++ showPair e s ++ ")"
    show' a = show a

-- |Given a pair and an environment, show it.
showPair (Ek Nil) _ = ""
showPair (Ep (a, b, _)) s@(_, m) =
  showFull (fst (m M.! a)) s ++
  case fst (m M.! b) of
    rest@(Ep _) -> " " ++ showPair rest s
    Ek Nil -> ""
    val -> " . " ++ showFull val s

-- |Miscellaneous values
data M
  = Boom T
  | Null
  | Undefined
  | Unspecified
  deriving (Eq)

instance Show M where
  show (Boom True) = "#t"
  show (Boom False) = "#f"
  show Null = "null"
  show Unspecified = "#<unspecified>"
  show Undefined = "#<undefined>"

-- |Procedures
type F = (L, [E] -> K -> C)

-- |Stores
type S = (Int, M.IntMap (E,T))

-- |Environment
type U = [(Ide, L)]

-- |Command continuation
type C = S -> A

-- |Expression continuation
type K = [E] -> C

-- |Answer
type A = (String, Maybe [E], S)

-- |Errors
type X = String

-- |Identifiers
type Ide = String

-- |Expressions
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
  deriving (Show)

-- |Commands
type Com = Expr
