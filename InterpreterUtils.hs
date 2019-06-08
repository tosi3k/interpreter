{- utilities for the interpreter -}
module InterpreterUtils where


import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Map hiding (map)
import Data.Maybe
import Data.List hiding (insert)

import AbsGrammar

{- the representation of the address in our runtime -}
type Location = Integer

{- container for all so far defined identifiers with their addresses -}
type Env = Map Ident Location

{-
  container for locations for all defined (so far) identifiers
  and their corresponding values (with redundant ones as well)
-}
type Store = Map Location Value

{- function representation in our runtime -}
type Function = (Type, [Arg], [Stmt], Env)

{- representation of values in our runtime -}
data Value = VInt Integer
           | VBool Bool
           | VString String
           | VTuple [Value]
           | VList [Value]
           | VFun Function deriving Eq

instance Show Value where
  show (VString s)   = show s
  show (VBool True)  = "true"
  show (VBool False) = "false"
  show (VInt n)      = show n
  show (VTuple vals) = "(" ++ (intercalate ", " $ map show vals) ++ ")"
  show (VList vals)  = "[" ++ (intercalate ", " $ map show vals) ++ "]"
  show (VFun f)      = show f

{- types of errors one can detect during program interpretation -}
data RuntimeError = MissingReturn Ident | ZeroDivision | FetchIndexOutOfRange

instance Show RuntimeError where
  show (MissingReturn (Ident ident)) = "Execution of function " ++ ident ++ " finished with no return"
  show ZeroDivision                  = "Division by zero appeared during program exection"
  show FetchIndexOutOfRange          = "Fetch index out of range"

{-
  monad for the context of interpreting code in JPP
  we enrich the IO monad w/ the usage of transformers with the following stuff:
  * possibility to throw runtime errors (using ExceptT transformer)
  * read&write store which maps locations to actual values (using StateT transformer)
  * read-only environment which maps identifiers to locations (using ReaderT transformer)
-}
type InterpreterMonad = ReaderT Env (StateT Store (ExceptT RuntimeError IO))

{- accessor for new free location (we don't free the redundant ones) -}
newLoc :: InterpreterMonad Location
newLoc = do
  store <- get
  case (size store) of
    0 -> return 0
    _ -> return $ 1 + (fst $ findMax store)

{- retrieve value of the identifier -}
getValue :: Ident -> InterpreterMonad Value
getValue ident = do
  store <- get
  env <- ask
  return $ store ! (env ! ident)

{- return an environment with newly declared identifier -}
declVal :: Ident -> Value -> InterpreterMonad Env
declVal ident val = do
  env <- ask
  store <- get
  loc <- newLoc
  put $ insert loc val store
  return $ insert ident loc env
