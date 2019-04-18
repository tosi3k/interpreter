{- quick & dirty type checker -}
module TypeChecker where


import Control.Monad.Except
import Control.Monad.Reader
import Data.Map
import Data.Maybe

import AbsGrammar
import TypeCheckerUtils


{- expression checking -}
inferType :: Expr -> StaticCheckMonad MockType
inferType ELitTrue = return MockBool

inferType ELitFalse = return MockBool

inferType (ELitInt _) = return MockInt

inferType (EString _) = return MockString

inferType (ENeg expr) = do
  exprType <- inferType expr
  if exprType == MockBool then
    return MockBool
  else
    throwError BadTypeInExpr

inferType (ENot expr) = do
  exprType <- inferType expr
  if exprType == MockInt then
    return MockInt
  else
    throwError BadTypeInExpr

inferType (EMul expr1 _ expr2) = do
  exprType1 <- inferType expr1
  exprType2 <- inferType expr2
  if exprType1 == MockInt && exprType2 == MockInt then
    return MockInt
  else
    throwError BadTypeInExpr

inferType (EAdd expr1 addOp expr2) = do
  exprType1 <- inferType expr1
  exprType2 <- inferType expr2
  if exprType1 == MockInt && exprType2 == MockInt then
    return MockInt
  else if addOp == OpAdd && exprType1 == MockString && exprType2 == MockString then
    return MockString
  else
    throwError BadTypeInExpr

inferType (ERel expr1 relOp expr2) = do
  exprType1 <- inferType expr1
  exprType2 <- inferType expr2
  if exprType1 == exprType2 then
    return MockBool
  else
    throwError BadTypeInExpr

inferType (EAnd expr1 expr2) = do
  exprType1 <- inferType expr1
  exprType2 <- inferType expr2
  if exprType1 == MockBool && exprType2 == MockBool then
    return MockBool
  else
    throwError BadTypeInExpr

inferType (EOr expr1 expr2) = inferType (EAnd expr1 expr2)

inferType (EVar ident) = do
  varType <- getIdentType ident
  case varType of
    MockFun _ _ _ -> throwError $ BadIdentifier ident
    _             -> return varType

inferType (EApp ident exprs) = do
  funType <- getIdentType ident
  case funType of
    MockFun retType args _ -> do
      checkArgs args exprs
      return $ typeToMockType retType
    _                      -> throwError $ BadIdentifier ident

checkArgs :: [Arg] -> [Expr] -> StaticCheckMonad ()
checkArgs ((ArgVal argType _):args) (expr:exprs) = do
  exprType <- inferType expr
  let expectedType = typeToMockType argType
  if exprType == expectedType then
    checkArgs args exprs
  else
    throwError $ BadArgType exprType expectedType
checkArgs ((ArgRef argType argIdent):args) (var@(EVar varIdent):exprs) = do
  exprType <- inferType var
  let expectedType = typeToMockType argType
  if exprType == expectedType then
    checkArgs args exprs
  else
    throwError $ BadArgType exprType expectedType
checkArgs [] [] = return ()
checkArgs [] _ = throwError BadNumberOfArgs
checkArgs _ [] = throwError BadNumberOfArgs
checkArgs _ _ = throwError BadReferenceArg


{- statement checking -}
checkStmt :: Stmt -> StaticCheckMonad Env
checkStmt Empty = do
  (env, _, _) <- ask
  return env

checkStmt (VDecl varType []) = do
  (env, _, _) <- ask
  return env
checkStmt (VDecl varType (item:items)) = do
  (env, _, _) <- ask
  case item of
    NoInit ident -> do
      let newEnv = insert ident (typeToMockType varType) env
      local (\(_, isLoop, retType) -> (newEnv, isLoop, retType)) $ checkStmt (VDecl varType items)
    Init ident expr -> do
      exprType <- inferType expr
      let newEnv = insert ident (typeToMockType varType) env
      if exprType == typeToMockType varType then
        local (\(_, isLoop, retType) -> (newEnv, isLoop, retType)) $ checkStmt (VDecl varType items)
      else
        throwError $ BadVarDecl ident (typeToMockType varType) exprType

checkStmt (Ret expr) = do
  (env, _, retType) <- ask
  exprType <- inferType expr
  if retType == Nothing then
    throwError ReturnOutsideOfFunction
  else if fromJust retType /= exprType then
    throwError $ BadReturnType (fromJust retType) exprType
  else do
    return env

checkStmt Cont = do
  (env, isLoop, _) <- ask
  if isLoop then
    return env
  else
    throwError BadContinue

checkStmt Break = do
  (env, isLoop, _) <- ask
  if isLoop then
    return env
  else
    throwError BadBreak

checkStmt (Print expr) = do
  (env, _, _) <- ask
  inferType expr
  return env

checkStmt (SExpr expr) = checkStmt (Print expr)

checkStmt (Assign ident expr) = do
  (env, _, _) <- ask
  exprType <- inferType expr
  identType <- getIdentType ident
  if exprType == identType then
    return env
  else
    throwError BadTypeInExpr

checkStmt (While expr stmt) = do
  (env, _, _) <- ask
  exprType <- inferType expr
  if exprType /= MockBool then
    throwError ExpressionNotBoolean
  else do
    local (\(_, _, mMockType) -> (env, True, mMockType)) $ checkStmt stmt
    return env

checkStmt (Cond expr stmt) = do
  (env, _, _) <- ask
  exprType <- inferType expr
  if exprType /= MockBool then
    throwError ExpressionNotBoolean
  else do
    checkStmt stmt
    return env

checkStmt (CondElse expr stmt1 stmt2) = do
  (env, _, _) <- ask
  exprType <- inferType expr
  if exprType /= MockBool then
    throwError ExpressionNotBoolean
  else do
    checkStmt stmt1
    checkStmt stmt2
    return env

checkStmt (FDecl funType ident args (Block stmts)) = let
    enrichEnv :: [Arg] -> Env -> Env
    enrichEnv [] env = env
    enrichEnv (arg:args) env = case arg of
      (ArgVal argType ident) -> enrichEnv args (insert ident (typeToMockType argType) env)
      (ArgRef argType ident) -> enrichEnv args (insert ident (typeToMockType argType) env)
    enrichEnv2 :: Env -> Env
    enrichEnv2 env = insert ident (MockFun funType args stmts) env
  in do
    (env, _, _) <- ask
    local (\_ -> (enrichEnv2 $ enrichEnv args env, False, Just $ typeToMockType funType)) $ checkStmts stmts
    return $ enrichEnv2 env

checkStmt (BStmt (Block stmts)) = do
  (env, _, _) <- ask
  checkStmts stmts
  return env

checkStmts :: [Stmt] -> StaticCheckMonad Env
checkStmts (stmt:stmts) = do
  (_, isLoop, retType) <- ask
  env <- checkStmt stmt
  local (const (env, isLoop, retType)) (checkStmts stmts)
checkStmts [] = do
  (env, _, _) <- ask
  return env


staticCheck :: Program -> IO (Either StaticCheckError Env)
staticCheck (Prog stmts) = runExceptT (runReaderT (checkStmts stmts) (empty, False, Nothing))