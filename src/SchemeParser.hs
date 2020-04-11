{-|
Module      : SchemeParser
Description : Scheme parser according to R5RS specs.

Uses the ParserCombinator Haskell library.  Special forms are
desugared into primitive expressions (@Expr@).

-}
{-# LANGUAGE LambdaCase #-}

module SchemeParser where

import Data.List.NonEmpty (fromList, NonEmpty((:|)))
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
schemeBool = (char '#') *> ((string "t" *> return (Const (Boolean True))) <|>
                            (string "f" *> return (Const (Boolean False))))

initp x = x `elem` concat [['a' .. 'z'], ['A' .. 'Z'], "!$%&*/:<=>?_~"]

digitp x = x `elem`  ['0' .. '9']

specialSubseqp x = x `elem` "+-.@"

subseqp c = initp c || digitp c || specialSubseqp c

schemeId = (:) <$> satisfy initp <*> many (satisfy subseqp)
     <|> string "+" <|>
  string "-" <|>
  try (string "...") <?> "identifier"

-- |Parse a matching identifier
matchId s = do n <- schemeId
               if s == n
               then pure s
               else unexpected n
-- |Reserved symbol
reserved = tok . matchId

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
    reserved "lambda"
    fs <- tok formals
    exprs <- schemeExpr `sepBy1` space
    return $
      let (cmds, expr) = unsnoc exprs
       in case fs of
            (args, Nothing)   -> Lambda args cmds expr
            ([], Just name)   -> LambdaVV name cmds expr
            (args, Just rest) -> LambdaV args rest cmds expr

schemeBegin =
  parens $ do
    reserved "begin"
    wrapBegin <$> schemeExpr `sepBy1` space

unsnoc :: [a] -> ([a], a)
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
  schemeNum <|> schemeBool <|> schemeNil <||> schemeString <||>
  (Const . Symbol <$> schemeId) <|>
  schemeQuotedList <|>
    -- Quoted list within a quoted list.
   do
    x <- schemeQuoted
    return $
      App (Id "cons") [Const (Symbol "quote"), App (Id "cons") [x, Const Nil]]

escChar = char '\\' *> (satisfy (`elem` "'\"\\") <|> (const '\n' <$> char 'n'))
litOne delim = (escChar <||> satisfy (/= delim))
litStr = (between (char '"') (symb "\"") (many (litOne '"')))

schemeString = Const . String <$> litStr


schemeQuoteSpecialForm = symb "'" >> schemeQuotable

schemeQuoted =
  schemeQuoteSpecialForm <|> parens (reserved "quote" >> schemeQuotable)

schemeNil = lparen *> rparen *> return (Const Nil)

schemeApp = do
  (e:es) <- parens (schemeExpr `sepBy1` space)
  return $ App e es

schemeSet =
  parens (reserved "set!" *> (Set <$> tok schemeId <*> schemeExpr))

schemeIf =
  parens $ do
    reserved "if"
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
  parens (reserved "let" *>
         (desugarLet <$> schemeLetBindings <*> many1 schemeExpr))

desugarLets bindings bodies =
  foldr (\(n, e) r -> App (Lambda [n] [] r) [e]) (wrapBegin bodies) bindings

schemeLetrecBinding :: Parser (String, Expr)
schemeLetrecBinding = parens (parens ((,) <$> tok schemeId <*> schemeExpr))

schemeLets =
  parens $ do
    reserved "let*"
    bindings <- schemeLetBindings
    desugarLets bindings <$> many1 schemeExpr

schemeLetrec =
  parens $ do
    reserved "letrec"
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

schemeCond = parens $ reserved "cond" >> desugarCond <$> schemeCondBranches

schemeAnd = 
  parens $ do
    reserved "and"
    exprs <- schemeExpr `sepBy` space
    pure (foldr (\e es -> If e es (Const (Boolean False)))
                (Const (Boolean True)) exprs)

-- Danger!  We're writing unhygienic macros!
schemeOr = 
  parens $ do
    reserved "or"
    exprs <- schemeExpr `sepBy` space
    pure (foldr g (Const (Boolean False)) exprs)
  where
    g e es = let name = ('"':show e)
             in App (Lambda [name] [] (If (Id name)
                                          (Id name)
                                          es))
                    [e]
schemeSpecialForm = schemeBegin <||> schemeAnd <||> schemeOr <||>
  schemeLambda <||> schemeIf <||> schemeSet <||> schemeLet <||> schemeLets <||> schemeLetrec <||>
  schemeCond <||>
  schemeApp

schemeCompoundExpr = try schemeQuoted <|> schemeSpecialForm

schemeExpr = schemeCompoundExpr <|> schemeNum <|> schemeBool <|>
             (Id <$> schemeId) <|> schemeString

wrapBegin :: [Expr] -> Expr
wrapBegin a = App (Lambda [] (init a) (last a)) []

schemeCommand = schemeExpr

parseExpr = wrapBegin <$> (space >> schemeExpr `sepEndBy1` space <* eof)

-- |Parse a string into a Scheme 'Expr', but return @Nothing@ if there
-- was unconsumed input.
readExpr :: String -> Either ParseError Expr
readExpr = parse parseExpr ""

readProg = parse schemeProgram ""

schemeProgram :: Parser Expr
schemeProgram = desugarProgram <$> (space >> prog) <* eof
  where prog = fromList <$> ((Right <$> schemeDefn) <||> (Left <$> schemeCommand)) `sepEndBy1` space

schemeDefn :: Parser Defn
schemeDefn =
  parens $ do
    reserved "define"
    fs <- tok formals
    exprs <- schemeExpr `sepBy1` space
    let (cmds, expr) = unsnoc exprs
    case fs of
       ([], Just v)   -> pure (Defn1 v expr)
       ([], Nothing) -> fail ("invalid pattern in: (define () " <> show exprs <> ")")
       ((f:args), Just rest) -> pure (Defn3 f args rest cmds expr)
       ((f:args), Nothing) -> pure (Defn2 f args cmds expr)

-- |Convert a program to a expression, binding all top level defines
-- to the value #<undefined>.
desugarProgram :: Program -> Expr
desugarProgram (x :| xs) = desugarLets declNames progBody
  where
    l = (x:xs)
    extractName (Defn1 i _) = i
    extractName (Defn2 i _ _ _) = i
    extractName (Defn3 i _ _ _ _) = i
    declNames = [(extractName d, Const Nil) | Right d <- l]
    progBody = either id desugarDefn <$> l

-- |Convert define to set!
desugarDefn :: Defn -> Com
desugarDefn (Defn1 x e) = Set x e
desugarDefn (Defn2 f args cmds e) = Set f (Lambda args cmds e )
desugarDefn (Defn3 f args rest cmds e) = Set f (LambdaV args rest cmds e)
