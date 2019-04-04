{-|
Module      : SchemeParser
Description : Scheme parser according to R5RS specs.

Uses the ParserCombinator Haskell library.

-}
{-# LANGUAGE LambdaCase #-}

module SchemeParser where
import           Data.Char
import           SchemeEval
import           SchemeTypes
import           Text.ParserCombinators.Parsec hiding (space)

a <||> b = try a <|> b

-- |Transforms a parser into one that also consumes trailing whitespace.
tok p = do
  x <- p
  space
  return x

eol = char '\n'

schemeComment = char ';' >> many (noneOf "\n") >>  eol

schemeWhitespace = oneOf " \n\t" <|> schemeComment <?> "whitespace"

-- |Parse whitespace.
space :: Parser ()
space = skipMany schemeWhitespace

-- |Parse a symbol, consuming leading whitespace.
symb :: String -> Parser String
symb = tok . string

-- |Parse a number.
nat :: Parser Integer
nat = read <$> many1 digit

-- |Like 'nat' but consumes leading whitespace.
natural = tok nat

-- |Parse a negative number.
negnat = string "-" >> (-) 0 <$> natural

-- |Parse a Scheme number.
schemeNum = Const . Number <$> negnat <||> natural

-- |Apply a parser, then when it succeeds, return a constant.
constLit k c = k >> return c

-- |Parse a boolean.
schemeBool = do
  char '#'
  (string "t" >> return (Const (Boolean True))) <|>
   (string "f" >> return (Const (Boolean False)))


initp x = x `elem` concat [['a' .. 'z'], ['A' .. 'Z'], "!$%&*/:<=>?_~"]

digitp x = x `elem` ['0' .. '9']

specialSubseqp x = x `elem` "+-.@"

subseqp c = initp c || digitp c || specialSubseqp c

schemeId =
  do {
     x <- satisfy initp;
     xs <- many (satisfy subseqp);
     return (x : xs) }
     <|> string "+"
     <|> string "-"
     <|> try (string "...")
     <?> "identifier"

lparen = symb "("

rparen = symb ")"

dot = symb "."

formals :: Parser ([Ide], Maybe Ide)
formals =
  do { x <- schemeId; return ([], Just x) } <|> do {
    lparen;
    noArgs <- optionMaybe rparen;
    (case noArgs of
      Just _ -> return ([], Nothing)
      Nothing -> do {
                   names <- sepEndBy1 schemeId space;
                   rest <- optionMaybe (dot >> schemeId);
                   rparen;
                   return (names, rest) })}

schemeLambda = do
  lparen
  symb "lambda"
  fs <- tok formals
  exprs <- schemeExpr `sepBy1` space
  rparen
  return $ let (cmds, expr) = unsnoc exprs
   in case fs of
        (args, Nothing)   -> Lambda args cmds expr
        ([], Just name)   -> LambdaVV name cmds expr
        (args, Just rest) -> LambdaV args rest cmds expr

unsnoc xs = loop [] xs
  where
    loop hs =
      \case
        [x] -> (reverse hs, x)
        (x:xs) -> loop (x : hs) xs
        [] -> error "empty"


reifyQuotedList :: [Expr] -> Expr
reifyQuotedList = foldr (\e es -> App (Id "cons") [e,es]) (Const Nil)

reifyImproperList :: [Expr] -> Expr
reifyImproperList = foldr1 (\e es -> App (Id "cons") [e,es])

schemeQuotedList = do {
  lparen;
  exprs <- schemeQuotable `sepBy1` space;
  last <- optionMaybe (dot >> schemeQuotable);
  rparen;
  return $ case last of
      Nothing -> reifyQuotedList exprs
      Just a  -> reifyImproperList (exprs ++ [a])
  }

schemeQuotable =
  schemeNum <|> schemeBool <|> schemeNil <||>
  do { Const . Symbol <$> schemeId } <|> schemeQuotedList <|>
  do {
   x <- schemeQuoted;
   return $ App (Id "cons") [Const (Symbol "quote"), App (Id "cons") [x, Const Nil]]
}

schemeQuoteSpecialForm = symb "'" >> schemeQuotable
schemeQuoted = schemeQuoteSpecialForm
  <|> do
        lparen
        symb "quote"
        x <- schemeQuotable
        rparen
        return x

schemeNil = lparen >> rparen >> return (Const Nil)

schemeApp = do
  lparen
  (e:es) <- schemeExpr `sepBy1` space
  rparen
  return $ App e es

schemeSet = do
  lparen
  symb "set!"
  n <- tok schemeId
  exp <- schemeExpr
  rparen
  return $ Set n exp

schemeIf =
  do {
     lparen;
     symb "if";
     p <- tok schemeExpr;
     c <- tok schemeExpr;
     a <- optionMaybe schemeExpr;
     rparen;
     return $ case a of
       Just a  ->  If p c a
       Nothing -> IfPartial p c
    }

{-
(define-syntax let
  (syntax-rules ()
    ((let ((name val) ...) body1 body2 ...)
     ((lambda (name ...) body1 body2 ...)
      val ...))
    ((let tag ((name val) ...) body1 body2 ...)
     ((letrec ((tag (lambda (name ...)
                      body1 body2 ...)))
        tag)))))
-}

schemeLetBindings :: Parser [(String, Expr)]
schemeLetBindings = do
  lparen
  r <- many $ do {
               lparen;
               n <- tok schemeId;
               e <- schemeExpr;
               rparen;
               return (n,e)
               }
  rparen
  return r

desugarLet :: [(String, Expr)] -> [Expr] -> Expr
desugarLet bindings bodies = App (Lambda names (butLast bodies) (last bodies)) exps
  where
  (names, exps) = unzip bindings

schemeLet = do
  lparen
  symb "let"
  bindings <- schemeLetBindings
  letBody <- many1 schemeExpr
  rparen
  return $ desugarLet bindings letBody

desugarCond :: [(Expr, Expr)] -> Expr
desugarCond = foldr (\p c -> (uncurry If) p c) (IfPartial (Const (Boolean False)) (Const Nil))

schemeCondBranches :: Parser [(Expr, Expr)]
schemeCondBranches = do
  r <- many1 $ do {
               lparen;
               p <- tok schemeExpr;
               e <- schemeExpr;
               rparen;
               return (p,e)
               }
  return r

schemeCond = do
  lparen
  symb "cond"
  branches <- schemeCondBranches
  rparen
  return $ desugarCond branches
  

schemeIdExpr = Id <$> schemeId

schemeSpecialForm = schemeLambda <||> schemeIf <||> schemeSet <||> schemeLet <||> schemeCond <||> schemeApp

schemeCompoundExpr = try schemeQuoted <|> schemeSpecialForm

schemeExpr = schemeCompoundExpr <|> schemeNum <|>  schemeBool <|> schemeIdExpr

-- Not efficient but we don't spend that much time in parsing.
butLast = reverse . tail . reverse

wrapBegin :: [Expr] -> Expr
wrapBegin a = App (Lambda [] (butLast a) (last a)) []

parseExpr = do
  space
  xs <- schemeExpr `sepEndBy1` space
  eof
  return $ wrapBegin xs

-- |Parse a string into a Scheme 'Expr', but return @Nothing@ if there
-- was unconsumed input.
readExpr :: String -> Either ParseError Expr
readExpr = parse parseExpr ""

-- |Parse and evaluate a string.
reval :: String -> A
reval s = case parse parseExpr "" s of
  Right res -> evalStd res
  Left err  -> ("Error: " ++ show err, Nothing, emptyStore)
