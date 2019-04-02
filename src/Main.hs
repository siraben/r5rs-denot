module Main where
import SchemeRepl

-- |The entry point for the Scheme REPL.
main :: IO ()
main = do
  putStrLn "Welcome to the r5rs-denot Scheme interpreter. Control-d to exit."
  repl
