{-|
Module      : SchemeParser
Description : Scheme parser according to R5RS specs.

This is an implementation of combinator parsing from scratch,
including various instance declarations for the 'Functor', 'Monad',
'Applicative', 'MonadZero' and 'MonadPlus' typeclasses.
-}
{-# LANGUAGE LambdaCase #-}

module SchemeParser where

import Data.Char
import SchemeTypes

newtype Parser a =
  Parser (String -> [(a, String)])

-- |Consume a single character.
item :: Parser Char
item =
  Parser $ \case
    "" -> []
    (c:cs) -> [(c, cs)]

parse (Parser p) = p

instance Functor Parser where
  fmap f (Parser cs) = Parser (\s -> [(f a, b) | (a, b) <- cs s])

instance Applicative Parser where
  pure = return
  (Parser cs1) <*> (Parser cs2) =
    Parser (\s -> [(f a, s2) | (f, s1) <- cs1 s, (a, s2) <- cs2 s1])

-- |A monad with a zero (i.e. "failure").
class Monad m =>
      MonadZero m
  where
  zero :: m a

instance Monad Parser where
  return a = Parser $ \cs -> [(a, cs)]
  p >>= f = Parser $ \cs -> concat [parse (f a) cs' | (a, cs') <- parse p cs]

class MonadZero m =>
      MonadPlus m
  where
  (<|>) :: m a -> m a -> m a

instance MonadZero Parser where
  zero = Parser (const [])

instance MonadPlus Parser where
  p <|> q = Parser (\cs -> parse p cs ++ parse q cs)

-- |Given two parsers @p@ and @q@, create a new parser such @q@ is
-- tried if @p@ failed.
(+++) :: Parser a -> Parser a -> Parser a
p +++ q =
  Parser
    (\cs ->
       case parse (p <|> q) cs of
         [] -> []
         (x:xs) -> [x])

-- |Lift a predicate into a parser.
sat :: (Char -> Bool) -> Parser Char
sat p = do
  c <- item
  if p c
    then return c
    else zero

-- |Consume a specific character.
char :: Char -> Parser Char
char c = sat (c ==)

-- |Consume a specific string.
string :: String -> Parser String
string "" = return ""
string (c:cs) = do
  char c
  string cs
  return (c : cs)

-- |Turns a parser into its Kleene star variant.
many :: Parser a -> Parser [a]
many p = many1 p +++ return []

-- |Turns a parser into its Kleene plus variant.
many1 :: Parser a -> Parser [a]
many1 p = do
  a <- p
  as <- many p
  return (a : as)

-- |Given two parsers @a@, @b@, return a parser @c@ such that it
-- accepts the language given by @a@ separated by @b@, and drops the
-- results of the separator.
sepby :: Parser a -> Parser b -> Parser [a]
p `sepby` sep = (p `sepby1` sep) +++ return []

-- |Like 'sepby', but at least one non-separator element must be
-- parsed.
sepby1 :: Parser a -> Parser b -> Parser [a]
p `sepby1` sep = do
  a <- p
  as <-
    many $ do
      sep
      p
  return (a : as)

chainl :: Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainl p op a = (p `chainl1` op) +++ return a

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
p `chainl1` op = do
  a <- p
  rest a
  where
    rest a =
      (do f <- op
          b <- p
          rest (f a b)) +++
      return a

-- |Parse a numeric digit.
digit :: Parser Char
digit = sat isDigit

schemeComment = do
  char ';'
  many (sat (\c -> c /= '\n'))
  return ' '
  
schemeWhitespace = char ' ' <|> char '\n' <|> char '\t' <|> schemeComment

-- |Parse whitespace.
space :: Parser String
space = many $ schemeWhitespace

-- |Lifts a parser into a whitespace-prefixed accepting one.
token :: Parser a -> Parser a
token p = do
  a <- p
  space
  return a

-- |Parse a symbol, consuming leading whitespace.
symb :: String -> Parser String
symb = token . string

-- |Parse characters up to the given terminator.
upTo :: Char -> Parser String
upTo c = many $ sat (/= c)

-- |Parse a number.
nat :: Parser Integer
nat = do
  xs <- many1 digit
  return (read xs :: Integer)

-- |Like 'nat' but consumes leading whitespace.
natural :: Parser Integer
natural = token nat

-- |Parse a negative number.
negnat = do
  string "-"
  n <- natural
  return $ -n

-- |Parse a Scheme number.
schemeNum :: Parser Expr
schemeNum = do
  x <- natural <|> negnat
  return $ Const (Number x)

-- |The list of reserved Scheme Booleans.
boolExprs :: [(String, Expr)]
boolExprs = [("#t", Const (Boolean True)), ("#f", Const (Boolean False))]

-- |Apply a parser, then when it succeeds, return a constant.
constLit k c = do
  k
  return c

-- |Parse a built-in constant (as defined in 'constExprs').
schemeBool :: Parser Expr
schemeBool =
  foldr (\(s, const) rest -> constLit (symb s) const <|> rest) zero boolExprs

initp x = x `elem` concat [['a' .. 'z'], ['A' .. 'Z'], "!$%&*/:<=>?_~"]

digitp x = x `elem` ['0' .. '9']

specialSubseqp x = x `elem` "+-.@"

subseqp c = initp c || digitp c || specialSubseqp c

schemeId =
  do x <- sat initp
     xs <- many (sat subseqp)
     return (x : xs)
     <|> string "+"
     <|> string "-"
     <|> string "..."

lparen = symb "("

rparen = symb ")"

dot = do
  space
  char '.'
  space

formals :: Parser ([Ide], Maybe Ide)
formals =
  do { x <- schemeId;
     return ([], Just x) } <|> do {
    lparen;
    rparen;
    return ([], Nothing)
     } <|> do {
    lparen;
    names <- schemeId `sepby1` space;
    dot;
    rest <- schemeId;
    rparen;
    return (names, Just rest) } <|> do {
    lparen;
    names <- schemeId `sepby1` space;
    rparen;
    return (names, Nothing)
}

schemeLambda = do
  lparen
  symb "lambda"
  fs <- formals
  space
  exprs <- schemeExpr `sepby1` space
  rparen
  let (cmds, expr) = unsnoc exprs
   in case fs of
        (args, Nothing) -> return $ Lambda args cmds expr
        ([], Just name) -> return $ LambdaVV name cmds expr
        (args, Just rest) -> return $ LambdaV args rest cmds expr

unsnoc xs = loop [] xs
  where
    loop hs =
      \case
        [x] -> (reverse hs, x)
        (x:xs) -> loop (x : hs) xs
        [] -> error "empty"

schemeQuotable =
  schemeNum <|> schemeBool <|> schemeNil <|> do
  {
    x <- schemeId;
    return $ Const (Symbol x)
  }

schemeQuoted =
  do char '\''
     schemeQuotable
     <|> do
    lparen
    string "quote"
    space
    x <- schemeQuotable
    rparen
    return x

schemeNil = do
  lparen
  rparen
  return $ Const Nil

schemeApp = do
  lparen
  exprs <- schemeExpr `sepby1` space
  rparen
  return $ App (head exprs) (tail exprs)

schemeSet = do
  lparen
  string "set!"
  space
  n <- schemeId
  space
  exp <- schemeExpr
  rparen
  return $ Set n exp

schemeIf =
  do {
    lparen;
     string "if";
     space;
     p <- schemeExpr;
     space;
     c <- schemeExpr;
     space;
     a <- schemeExpr;
     rparen;
     return $ If p c a
    } <|> do
    lparen
    string "if"
    space
    p <- schemeExpr
    space
    c <- schemeExpr
    rparen
    return $ IfPartial p c

schemeExpr :: Parser Expr
schemeExpr =
  schemeLambda <|> schemeIf <|> schemeSet <|> schemeQuoted <|> schemeApp <|>
  schemeNum <|>
  schemeBool <|> do {
    x <- schemeId;
    return $ Id x }

parseExpr = do
  space
  schemeExpr

-- |Parse a string into a Scheme 'Expr', but return @Nothing@ if there
-- was unconsumed input.
readExpr :: String -> Maybe Expr
readExpr s =
  case parse parseExpr s of
    (res, ""):_ -> Just res
    _ -> Nothing
