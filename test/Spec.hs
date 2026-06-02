module Main where

import Control.Monad (forM_)
import SchemeEval
import SchemeTests
import SchemeTypes
import System.Exit (exitFailure)

main :: IO ()
main = do
  failures <- concat <$> traverse runCase cases
  if null failures
    then putStrLn ("Passed " <> show (length cases) <> " tests")
    else do
      forM_ failures putStrLn
      exitFailure

type Case = (String, Expr, [String])

cases :: [Case]
cases =
  [ ("identity", idTest, ["3"])
  , ("first argument", fstTest, ["3"])
  , ("second argument", sndTest, ["5"])
  , ("curried first", sFstTest, ["3"])
  , ("curried second", sSndTest, ["5"])
  , ("addition primitive", addTest, ["8"])
  , ("lambda application", addTest2, ["20"])
  , ("car", carTest, ["10"])
  , ("cdr", cdrTest, ["(20)"])
  , ("if true branch", ifTest, ["10"])
  , ("factorial via y combinator", factYComb, ["720"])
  , ("program define", rparse "(define x 4) (+ x 6)", ["10"])
  , ("let", rparse "(let ((x 2) (y 3)) (* x y))", ["6"])
  , ("call with values", rparse "(call-with-values (lambda () (values 1 2)) +)", ["3"])
  ]

runCase :: Case -> IO [String]
runCase (name, expr, expected) = do
  let (actual, store) = evalStd expr
      rendered = (`showFull` store) <$> actual
  pure
    [ name <> ": expected " <> show expected <> ", got " <> show rendered
    | rendered /= expected
    ]
