module Main where
import SchemeEval
import SchemeTypes
import SchemeParser

import           System.Exit
import           System.IO

-- |Parse and evaluate a string.
reval :: String -> A
reval s = case parse schemeExpr s of
  (res, ""  ) : _ -> evalStd res
  (_  , rest) : _ -> ("Unexpected characters: " ++ rest, [], emptyStore)
  []              -> ("Parsing failed" , [], emptyStore)

-- |Print the contents of a value of type 'Result' 'Val', or an error
-- message.
reportResult :: A -> IO ()
reportResult (a, e, s) = putStrLn $ a ++ "\n\n" ++ show e ++ "\n"

-- |The main REPL loop.
repl :: IO ()
repl = do
  putStr "Scheme> "
  hFlush stdout
  done <- isEOF
  if done
  then do { putStrLn "Exiting."; exitSuccess }
  else do
    exp <- getLine
    if exp == "" then repl else reportResult $ reval exp
    repl

-- |Read, evaluate, print a file.
repf :: String -> IO ()
repf filename = do
  x <- openFile filename ReadMode
  y <- hGetContents x
  reportResult $ reval y

-- |The entry point for the Scheme REPL.
main :: IO ()
main = do
  putStrLn "Welcome to the r5rs-denot Scheme interpreter. Control-d to exit."
  repl
