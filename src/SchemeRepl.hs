module SchemeRepl where
import SchemeParser
import SchemeEval
import SchemeTypes
import           System.Exit
import           System.IO

-- |Parse and evaluate a string.
reval :: String -> A
reval s = case parse parseExpr s of
  (res, ""  ) : _ -> evalStd res
  (_  , rest) : _ -> ("Unexpected characters: " ++ rest, Nothing, emptyStore)
  []              -> ("Parsing failed" , Nothing, emptyStore)

-- |Print the contents of a value of type 'Result' 'Val', or an error
-- message.
reportResult :: A -> IO ()
reportResult (a, Nothing, s) = putStrLn $ "Error: " ++ a
reportResult (a, Just e, s) = let memusage = (length s - length builtInOps - 1)
                                  pluralize s x = s ++ if x > 1 || x == 0 then "s" else ""
  in
  putStrLn $ concat
                              [showFull (head e) s, a, "\nMemory used: ", show memusage, pluralize " cell" memusage]

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
