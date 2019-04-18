{- utilities for the interpreter -}
module InterpreterTypes where


import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Map
import Data.Maybe

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
data Value = VInt Integer | VBool Bool | VString String | VFun Function

instance Show Value where
  show (VString s) = s
  show (VBool b)   = show b
  show (VInt n)    = show n
  show (VFun f)    = show f

{- types of errors one can detect during program interpretation -}
data RuntimeError = MissingReturn Ident | ZeroDivision

instance Show RuntimeError where
  show (MissingReturn ident) = "Execution of function " ++ show ident ++ " finished with no return"
  show ZeroDivision          = "Division by zero appeared during program exection"


type SemanticState = ReaderT Env (StateT Store (ExceptT RuntimeError IO))

{- accessor for new free location (we don't free the redundant ones) -}
newLoc :: SemanticState Location
newLoc = do
  store <- get
  case (size store) of
    0 -> return 0
    _ -> return $ 1 + (fst $ findMax store)

getValue :: Ident -> SemanticState Value
getValue ident = do
  store <- get
  env <- ask
  return $ store ! (env ! ident)

declVal :: Ident -> Value -> SemanticState Env
declVal ident val = do
  env <- ask
  store <- get
  loc <- newLoc
  put $ insert loc val store
  return $ insert ident loc env

declRefArg :: Ident -> Ident -> Env -> SemanticState Env
declRefArg refIdent argIdent modEnv = do
  env <- ask
  let refLoc = env ! refIdent
  return $ insert argIdent refLoc modEnv

declValArg :: Ident -> Value -> Env -> SemanticState Env
declValArg ident val modEnv = do
  store <- get
  loc <- newLoc
  put $ insert loc val store
  return $ insert ident loc modEnv
