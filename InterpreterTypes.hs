module InterpreterTypes where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Map
import Data.Maybe

import LexGrammar
import ParGrammar
import SkelGrammar
import PrintGrammar
import AbsGrammar
import ErrM

-- semantic domains
type Env = Map Ident Location

type Store = Map Location Value


type Location = Integer

type Function = (Type, [Arg], [Stmt], Env)


data Value = VInt Integer | VBool Bool | VString String | VFun Function

instance Show Value where
  show (VString s) = s
  show (VBool b)   = show b
  show (VInt n)    = show n
  show (VFun f)    = show f


data RuntimeError = MissingReturn | ZeroDivision


type SemanticState = ReaderT Env (StateT Store (ExceptT RuntimeError IO))


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
