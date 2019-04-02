module SchemeTypes where

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
  deriving (Eq)

instance Show Con where
  show (Symbol q)      = q
  show (Character h)   = "#\\" ++ [h]
  show (Number r)      = show r
  show (Boolean True)  = "#t"
  show (Boolean False) = "#t"
  show Nil             = "()"

-- Expressed values
data E
  = Ek Con
  | Ep (L, L, T)
  | Ev ([L], T)
  | Es ([L], T)
  | Em M
  | Ef F

instance Show E where
  show (Ek con)           = show con
  show (Ep (car, cdr, _)) = concat ["(", show car, " . ", show cdr, ")"]
  show (Ev (l, _))        = show l
  show (Es (l, _))        = show l
  show (Em m)             = show m
  show (Ef f)             = "#<procedure>"

-- Miscellaneous
data M
  = Boom T
  | Null
  | Undefined
  | Unspecified
  deriving (Eq)

instance Show M where
  show (Boom True)  = "#t"
  show (Boom False) = "#f"
  show Null         = "null"
  show Unspecified  = "#<unspecified>"
  show Undefined    = "#<undefined>"

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
type A = (String, [E], S)

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


data AST = Keyword String
         | Identifier String
         | Nat Integer
         | Call AST [AST]
         | LambdaExp [String] [AST] AST
         | LambdaExpR String [AST] AST
         | LambdaExpO [AST] String [AST] AST
         | Assign String AST
         | EmptyList
         deriving Show

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
