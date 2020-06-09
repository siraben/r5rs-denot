{-|
Module      : Main
Description : Main entry point for r5rs-denot Scheme.

-}
module Main where
import SchemeRepl

main :: IO ()
main = do
  putStrLn "Welcome to the r5rs-denot, the R5RS Scheme interpreter based on\ndenotational semantics.  Input an expression and press Enter to\nevaluate.  Press Control-d to exit.\n"
  repl
