{- interpreter implementation (most of the magic happens here) -}
module Interpreter where


import Data.Maybe
import Data.Map hiding (map)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import AbsGrammar
import InterpreterUtils

interpretExpr :: Expr -> InterpreterMonad Value
interpretExpr (ELitTrue) = return $ VBool True

interpretExpr (ELitFalse) = return $ VBool False

interpretExpr (ELitInt n) = return $ VInt n

interpretExpr (EString s) = return $ VString s

interpretExpr (ENeg expr) = do
  (VInt n) <- interpretExpr expr
  return $ VInt (-n)

interpretExpr (EAdd expr1 addOp expr2) = do
  val1 <- interpretExpr expr1
  val2 <- interpretExpr expr2
  case (val1, val2) of
    (VString s1, VString s2) -> return $ VString $ s1 ++ s2
    (VInt n1, VInt n2)       -> case addOp of
      OpAdd -> return $ VInt $ n1 + n2
      OpSub -> return $ VInt $ n1 - n2
    (VList vals1, VList vals2) ->
      return $ VList $ vals1 ++ vals2

interpretExpr (EMul expr1 mulOp expr2) = do
  (VInt val1) <- interpretExpr expr1
  (VInt val2) <- interpretExpr expr2
  case mulOp of
    OpMul -> return $ VInt $ val1 * val2
    OpDiv ->
      if val2 /= 0 then
        return $ VInt $ val1 `div` val2
      else
        throwError ZeroDivision

interpretExpr (EVar ident) = getValue ident

interpretExpr (ENot expr) = do
  (VBool b) <- interpretExpr expr
  return $ VBool $ not b

interpretExpr (EAnd expr1 expr2) = do
  (VBool b1) <- interpretExpr expr1
  if not b1 then
    return $ VBool False
  else do
    (VBool b2) <- interpretExpr expr2
    return $ VBool b2

interpretExpr (EOr expr1 expr2) = do
  (VBool b1) <- interpretExpr expr1
  if b1 then
    return $ VBool True
  else do
    (VBool b2) <- interpretExpr expr2
    return $ VBool b2

interpretExpr (ERel expr1 relOp expr2) = let
    evalOp :: (Eq a, Ord a) => RelOp -> a -> a -> Bool
    evalOp OpLt = (<)
    evalOp OpLe = (<=)
    evalOp OpGt = (>)
    evalOp OpGe = (>=)
    evalOp OpEq = (==)
    evalOp OpNeq = (/=)
  in do
    val1 <- interpretExpr expr1
    val2 <- interpretExpr expr2
    case (val1, val2) of
      (VInt a, VInt b) -> return $ VBool $ evalOp relOp a b
      (VString a, VString b) -> return $ VBool $ evalOp relOp a b
      (VBool a, VBool b) -> return $ VBool $ evalOp relOp a b
      (VTuple vals1, VTuple vals2) -> case relOp of
        OpEq  -> return $ VBool $ vals1 == vals2
        OpNeq -> return $ VBool $ vals1 /= vals2
      (VList vals1, VList vals2) -> case relOp of
        OpEq  -> return $ VBool $ vals1 == vals2
        OpNeq -> return $ VBool $ vals1 /= vals2
        

interpretExpr (EApp funId exprs) = let
    {- supply environment with new argument passed by reference -}
    declRefArg :: Ident -> Ident -> Env -> InterpreterMonad Env
    declRefArg refIdent argIdent modEnv = do
      env <- ask
      let refLoc = env ! refIdent
      return $ insert argIdent refLoc modEnv

    {- supply environment with new argument passed by value (hence new location) -}
    declValArg :: Ident -> Value -> Env -> InterpreterMonad Env
    declValArg ident val modEnv = do
      store <- get
      loc <- newLoc
      put $ insert loc val store
      return $ insert ident loc modEnv

    addArgsToEnv :: [Arg] -> [Expr] -> Env -> InterpreterMonad Env
    addArgsToEnv [] [] env = return env
    addArgsToEnv ((ArgVal _ ident):args) (expr:exprs) env = do
      val <- interpretExpr expr
      newEnv <- declValArg ident val env
      addArgsToEnv args exprs newEnv
    addArgsToEnv ((ArgRef _ ident):args) ((EVar refIdent):exprs) env = do
      newEnv <- declRefArg refIdent ident env
      addArgsToEnv args exprs newEnv

    addFunToEnv :: Ident -> Value -> Env -> InterpreterMonad Env
    addFunToEnv ident val@(VFun _) env = do
      env <- declValArg ident val env
      return env
  in do
    val@(VFun (_, args, stmts, fEnv)) <- getValue funId
    envWithArgs <- addArgsToEnv args exprs fEnv
    newEnv <- addFunToEnv funId val $ envWithArgs
    (_, mval, _, _) <- local (const newEnv) $ interpretStmts stmts
    case mval of
      Nothing -> throwError $ MissingReturn funId
      Just val -> return val

interpretExpr (ETuple exprs) = do
  vals <- forM exprs interpretExpr
  return $ VTuple vals

interpretExpr (EGet expr index) = do
  VTuple vals <- interpretExpr expr
  return $ vals !! (fromIntegral index)

interpretExpr (ELength expr) = do
  VList list <- interpretExpr expr
  return $ VInt $ fromIntegral $ length list

interpretExpr (EFetch listExpr indexExpr) = do
  VList vals <- interpretExpr listExpr
  VInt index <- interpretExpr indexExpr
  let legitIndex = fromIntegral index
  if legitIndex < 0 || legitIndex >= length vals then
    throwError FetchIndexOutOfRange
  else
    return $ vals !! legitIndex

interpretExpr (EList exprs) = do
  vals <- forM exprs interpretExpr
  return $ VList vals

interpretExpr (EEmptyList listType) = do
  return $ VList []


{-
 - output is a 4-tuple containing following information, respectively:
 - 1) hitherto environment,
 - 2) possible value produced by a "return" statement,
 - 3) bit indicating if "break" statement was launched,
 - 4) bit indicating if "continue" statement was launched.
-}
interpretStmt :: Stmt -> InterpreterMonad (Env, Maybe Value, Bool, Bool)
interpretStmt Empty = do
  env <- ask
  return (env, Nothing, False, False)

interpretStmt (Print expr) = do
  env <- ask
  val <- interpretExpr expr
  liftIO $ putStrLn $ show val
  return (env, Nothing, False, False)

interpretStmt (SExpr expr) = do
  interpretExpr expr
  env <- ask
  return (env, Nothing, False, False)

interpretStmt (Cond expr stmt) = do
  (VBool b) <- interpretExpr expr
  env <- ask
  if b then
    interpretStmt stmt
  else
    return (env, Nothing, False, False)

interpretStmt (CondElse expr stmt1 stmt2) = do
  (VBool b) <- interpretExpr expr
  interpretStmt $ if b then stmt1 else stmt2

interpretStmt w@(While expr stmt) = do
  env <- ask
  (VBool b) <- interpretExpr expr
  if b then do
    (env, mval, breakBit, contBit) <- interpretStmt stmt
    if breakBit then
      return (env, mval, False, False)
    else if contBit then
      interpretStmt w
    else case mval of
      Nothing -> interpretStmt w
      _ -> return (env, mval, False, False)
  else
    return (env, Nothing, False, False)

interpretStmt (BStmt (Block stmts)) = do
  env <- ask
  (_, mval, breakBit, contBit) <- interpretStmts stmts
  return (env, mval, breakBit, contBit)

interpretStmt (Ret expr) = do
  env <- ask
  val <- interpretExpr expr
  return (env, Just val, False, False)

interpretStmt (Assign ident expr) = do
  env <- ask
  val <- interpretExpr expr
  store <- get
  let loc = env ! ident
  put $ insert loc val store
  return (env, Nothing, False, False)

interpretStmt (VDecl _ []) = do
  env <- ask
  return (env, Nothing, False, False)
interpretStmt (VDecl vtype (item:items)) = let
    defaultValue :: Type -> Value
    defaultValue TInt           = VInt 0
    defaultValue TBool          = VBool False
    defaultValue TString        = VString ""
    defaultValue (TTuple types) = VTuple (map defaultValue types)
    defaultValue (TList ltype)  = VList []

    ident :: Item -> Ident
    ident (Init ident _) = ident
    ident (NoInit ident) = ident
  in do
    val <- case item of
      Init ident expr -> interpretExpr expr
      NoInit ident -> return $ defaultValue vtype
    env <- declVal (ident item) val
    local (const env) $ interpretStmt (VDecl vtype items)

interpretStmt (FDecl funType ident args (Block stmts)) = do
  env <- ask
  newEnv <- declVal ident $ VFun (funType, args, stmts, env)
  return (newEnv, Nothing, False, False)

interpretStmt Break = do
  env <- ask
  return (env, Nothing, True, False)

interpretStmt Cont = do
  env <- ask
  return (env, Nothing, False, True)


interpretStmts :: [Stmt] -> InterpreterMonad (Env, Maybe Value, Bool, Bool)
interpretStmts (stmt:stmts) = do
  aux@(env, mval, breakBit, contBit) <- interpretStmt stmt
  if breakBit || contBit || isJust mval then
    return aux
  else
    local (const env) (interpretStmts stmts)
interpretStmts [] = do
  env <- ask
  return (env, Nothing, False, False)



interpretProgram :: Program -> IO (Either RuntimeError ((Env, Maybe Value, Bool, Bool), Store))
interpretProgram (Prog stmts) = runExceptT $ runStateT (runReaderT (interpretStmts stmts) empty) empty
