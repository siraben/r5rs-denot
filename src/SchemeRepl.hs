{-|
Module      : SchemeRepl
Description : User-visible interface to r5rs-denot Scheme.

-}
module SchemeRepl where

import SchemeEval
import SchemeParser
import SchemeTypes
import System.Exit
import System.IO

-- |Print the contents of a value of type 'Result' 'Val', or an error
-- message.
reportResult :: A -> IO ()
reportResult (Nothing, s) = putStrLn $ "Error: "
reportResult (Just e, s) =
  let memusage = (new s - length builtInOps - length exprDefinedOps - 2)
      pluralize s x =
        s ++
        if x > 1 || x == 0
          then "s"
          else ""
   in do mapM_ putStrLn ((`showFull` s) <$> e)
         putStrLn $ "Memory used: " <> show memusage <> pluralize " cell" memusage

-- |The main REPL loop.
repl :: IO ()
repl = do
  putStr "r5rs-denot> "
  hFlush stdout
  done <- isEOF
  if done
    then putStrLn "Exiting." *> exitSuccess
    else do
      exp <- getLine
      if exp == ""
        then repl
        else reportResult $ reval exp
      repl

-- |Read, evaluate and print a file.
repf :: String -> IO ()
repf filename = do
  x <- openFile filename ReadMode
  y <- hGetContents x
  reportResult $ reval y

-- |Read and print a file.
rpf :: String -> IO ()
rpf filename = do
  x <- openFile filename ReadMode
  y <- hGetContents x
  case readProg y of
    Right a -> print a
    Left a -> putStrLn $ "Failed to parse file: " ++ show a
