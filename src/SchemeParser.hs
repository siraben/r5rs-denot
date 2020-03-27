{-|
Module      : SchemeParser
Description : Scheme parser according to R5RS specs.

Uses the ParserCombinator Haskell library.  Special forms are
desugared into primitive expressions (@Expr@).

-}
{-# LANGUAGE LambdaCase #-}

module SchemeParser where

import Data.Char
import SchemeTypes
import Text.ParserCombinators.Parsec hiding (space)
import Data.Functor

a <||> b = try a <|> b

-- |Transforms a parser into one that also consumes trailing whitespace.
tok p = p <* space

parens p = lparen *> p <* rparen

eol = char '\n'

schemeComment = char ';' *> many (noneOf "\n") *> eol

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
constLit :: Functor f => f a -> b -> f b
constLit = ($>)

-- |Parse a boolean.
schemeBool = (char '#') *> ((string "t" *> return (Const (Boolean True))) <|> (string "f" *> return (Const (Boolean False))))

initp x = x `elem` concat [['a' .. 'z'], ['A' .. 'Z'], "!$%&*/:<=>?_~"]

digitp x = x `elem`  ['0' .. '9']

specialSubseqp x = x `elem` "+-.@"

subseqp c = initp c || digitp c || specialSubseqp c

schemeId = (:) <$> satisfy initp <*> many (satisfy subseqp)
     <|> string "+" <|>
  string "-" <|>
  try (string "...") <?> "identifier"

lparen = symb "("

rparen = symb ")"

dot = symb "."

formals :: Parser ([Ide], Maybe Ide)
formals =
  do x <- schemeId
     return ([], Just x)
     <|> do
    lparen
    noArgs <- optionMaybe rparen
    case noArgs of
      Just _ -> return ([], Nothing)
      Nothing -> do
        names <- sepEndBy1 schemeId space
        rest <- optionMaybe (dot >> schemeId)
        rparen
        return (names, rest)

schemeLambda =
  parens $ do
    symb "lambda"
    fs <- tok formals
    exprs <- schemeExpr `sepBy1` space
    return $
      let (cmds, expr) = unsnoc exprs
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
reifyQuotedList = foldr (\e es -> App (Id "cons") [e, es]) (Const Nil)

reifyImproperList :: [Expr] -> Expr
reifyImproperList = foldr1 (\e es -> App (Id "cons") [e, es])

schemeQuotedList =
  parens $ do
    exprs <- schemeQuotable `sepBy1` space
    last <- optionMaybe (dot >> schemeQuotable)
    return $
      case last of
        Nothing -> reifyQuotedList exprs
        Just a  -> reifyImproperList (exprs ++ [a])

schemeQuotable =
  schemeNum <|> schemeBool <|> schemeNil <||> (Const . Symbol <$> schemeId) <|>
  schemeQuotedList <|>
    -- Quoted list within a quoted list.
   do
    x <- schemeQuoted
    return $
      App (Id "cons") [Const (Symbol "quote"), App (Id "cons") [x, Const Nil]]

schemeQuoteSpecialForm = symb "'" >> schemeQuotable

schemeQuoted =
  schemeQuoteSpecialForm <|> parens (symb "quote" >> schemeQuotable)

schemeNil = lparen *> rparen *> return (Const Nil)

schemeApp = do
  (e:es) <- parens (schemeExpr `sepBy1` space)
  return $ App e es

schemeSet =
  parens (symb "set!" *> (Set <$> tok schemeId <*> schemeExpr))

schemeIf =
  parens $ do
    symb "if"
    p <- tok schemeExpr
    c <- tok schemeExpr
    a <- optionMaybe schemeExpr
    return $
      case a of
        Just a  -> If p c a
        Nothing -> IfPartial p c

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
schemeLetBindings =
  parens (many (parens ((,) <$> tok schemeId <*> schemeExpr)))

desugarLet :: [(String, Expr)] -> [Expr] -> Expr
desugarLet bindings bodies = App (Lambda names (init bodies) (last bodies)) exps
  where
    (names, exps) = unzip bindings

schemeLet =
  parens (symb "let" *>
         (desugarLet <$> schemeLetBindings <*> many1 schemeExpr))

desugarLets bindings bodies =
  foldr (\(n, e) r -> App (Lambda [n] [] r) [e]) (wrapBegin bodies) bindings

schemeLetrecBinding :: Parser (String, Expr)
schemeLetrecBinding = parens (parens ((,) <$> tok schemeId <*> schemeExpr))

schemeLets =
  parens $ do
    symb "let*"
    bindings <- schemeLetBindings
    desugarLets bindings <$> many1 schemeExpr

schemeLetrec =
  parens $ do
    symb "letrec"
    binding <- schemeLetrecBinding
    let fname = fst binding
        fbody = snd binding
      in
        desugarLet [(fname, App (Id "recursive") [Lambda [fname] [] fbody])] <$> many1 schemeExpr

desugarCond :: [(Expr, Expr)] -> Expr
desugarCond = foldr (uncurry If) (IfPartial (Const (Boolean False)) (Const Nil))

-- FIXME: Handle else and =>
schemeCondBranches :: Parser [(Expr, Expr)]
schemeCondBranches =
  many1 $
  parens $ do
    p <- tok schemeExpr
    e <- schemeExpr
    return (p, e)

schemeCond = parens $ symb "cond" >> desugarCond <$> schemeCondBranches

schemeIdExpr = Id <$> schemeId

schemeSpecialForm =
  schemeLambda <||> schemeIf <||> schemeSet <||> schemeLet <||> schemeLets <||> schemeLetrec <||>
  schemeCond <||>
  schemeApp

schemeCompoundExpr = try schemeQuoted <|> schemeSpecialForm

schemeExpr = schemeCompoundExpr <|> schemeNum <|> schemeBool <|> schemeIdExpr

wrapBegin :: [Expr] -> Expr
wrapBegin a = App (Lambda [] (init a) (last a)) []

parseExpr = wrapBegin <$> (space >> schemeExpr `sepEndBy1` space <* eof)

-- |Parse a string into a Scheme 'Expr', but return @Nothing@ if there
-- was unconsumed input.
readExpr :: String -> Either ParseError Expr
readExpr = parse parseExpr ""
