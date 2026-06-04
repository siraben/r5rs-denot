module Main where

import Control.Monad (forM)
import SchemeEval (reval)
import SchemeTypes (E, S, showFull)
import Paths_r5rs_denot (getDataFileName)
import System.Exit (exitFailure)

data Case =
  Case FilePath [String]

cases :: [Case]
cases =
  [ Case "test/conformance/pass/basic-numeric.scm" ["(3 2 1 #f #t #t)"]
  , Case "test/conformance/pass/top-level-define.scm" ["720"]
  , Case "test/conformance/pass/mutable-pairs.scm" ["(9 8)"]
  , Case "test/conformance/pass/continuations-values.scm" ["(42 3 9)"]
  , Case "test/conformance/pass/derived-conditionals.scm" ["(2 3 1 5 7)"]
  ]

main :: IO ()
main = do
  results <- forM cases runCase
  let failures = [failure | Just failure <- results]
  if null failures
    then putStrLn ("Passed " <> show (length cases) <> " R5RS conformance cases.")
    else do
      mapM_ putStrLn failures
      exitFailure

runCase :: Case -> IO (Maybe String)
runCase (Case path expected) = do
  sourcePath <- getDataFileName path
  source <- readFile sourcePath
  let actual = render (reval source)
  pure $
    if actual == expected
      then Nothing
      else Just $
           unlines
             [ path
             , "  expected: " <> show expected
             , "  actual:   " <> show actual
             ]

render :: ([E], S) -> [String]
render (values, store) = (`showFull` store) <$> values
