module SchemeRepl where
import SchemeParser
import SchemeEval
import SchemeTypes
import           System.Exit
import           System.IO

-- |Print the contents of a value of type 'Result' 'Val', or an error
-- message.
reportResult :: A -> IO ()
reportResult (a, Nothing, s) = putStrLn $ "Error: " ++ a
reportResult (a, Just e, s) = let memusage = (length s - length builtInOps - 1)
                                  pluralize s x = s ++ if x > 1 || x == 0 then "s" else ""
  in
  putStrLn $ concat  [showFull (head e) s, a, "\nMemory used: ", show memusage, pluralize " cell" memusage]

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

-- |Read, evaluate and print a file.
repf :: String -> IO ()
repf filename = do
  x <- openFile filename ReadMode
  y <- hGetContents x
  reportResult $ reval y

-- |Read  and print a file.
rpf :: String -> IO ()
rpf filename = do
  x <- openFile filename ReadMode
  y <- hGetContents x
  (case readExpr y of
     Right a -> putStrLn $ show a
     Left a -> putStrLn $ "Failed to parse file: " ++ show a
     )
