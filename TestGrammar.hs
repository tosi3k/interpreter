module Main where


import System.IO(stdin, stderr, hPutStrLn, hPutStr, hGetContents)
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

runFile :: ParseFun Program -> FilePath -> IO ()
runFile p f = readFile f >>= run p

run :: ParseFun Program -> String -> IO ()
run p s = let ts = myLLexer s in case p ts of
  Bad s   -> do hPutStrLn stderr "Parse failed."
                exitFailure
  Ok tree -> do staticCheckResult <- staticCheck tree
                case staticCheckResult of
                  Left err -> do hPutStr stderr "Static checking error: "
                                 hPutStrLn stderr $ show err
                                 exitFailure
                  Right _  -> do it <- interpretProgram tree
                                 case it of
                                   Left err -> do hPutStr stderr "Runtime error: "
                                                  hPutStrLn stderr $ show err
                                                  exitFailure
                                   Right _  -> do exitSuccess

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin verbosely."
    , "  (file)          Parse content of a file verbosely."
    ]
  exitSuccess

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    [] -> hGetContents stdin >>= run pProgram
    fs -> mapM_ (runFile pProgram) fs
