module Main where


import System.IO(stdin, hGetContents)
import System.Environment(getArgs, getProgName)
import System.Exit(exitFailure, exitSuccess)

import LexGrammar
import ParGrammar
import PrintGrammar
import AbsGrammar
import ErrM
import TypeChecker
import Interpreter

type ParseFun a = [Token] -> Err a

myLLexer = myLexer

type Verbosity = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = if v > 1 then putStrLn s else return ()

runFile :: Verbosity -> ParseFun Program -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run v p

run :: Verbosity -> ParseFun Program -> String -> IO ()
run v p s = let ts = myLLexer s in case p ts of
  Bad s   -> do putStrLn "\nParse failed...\n"
                putStrV v "Tokens:"
                putStrV v $ show ts
                putStrLn s
                exitFailure
  Ok tree -> do staticCheckResult <- staticCheck tree
                case staticCheckResult of
                  Left err -> do putStrLn "Static checking error..."
                                 putStrLn $ show err
                                 exitFailure
                  Right _  -> do it <- interpretProgram tree
                                 case it of
                                   Left err -> do putStrLn "Runtime error..."
                                                  putStrLn $ show err
                                                  exitFailure
                                   Right _  -> do exitSuccess


showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree = do
  putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
  putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin verbosely."
    , "  (files)         Parse content of files verbosely."
    , "  -s (files)      Silent mode. Parse content of files silently."
    ]
  exitFailure

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    [] -> hGetContents stdin >>= run 2 pProgram
    "-s":fs -> mapM_ (runFile 0 pProgram) fs
    fs -> mapM_ (runFile 2 pProgram) fs
