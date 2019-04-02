module Main where
import SchemeRepl

-- |The entry point for the Scheme REPL.
main :: IO ()
main = do
  putStrLn "Welcome to the r5rs-denot,\nThe denotational semantics-based R5RS Scheme interpreter.\nInput an expression and press Enter to evaluate. Control-d to exit.\n"
  repl
