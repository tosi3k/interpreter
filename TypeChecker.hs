module TypeChecker where

import Control.Monad.Except
import Control.Monad.Reader
import Data.Map
import Data.Maybe

import LexGrammar
import ParGrammar
import SkelGrammar
import PrintGrammar
import AbsGrammar
import ErrM

-- quick & dirty type checker

data StaticCheckError = BadTypeInExpr
                      | BadNumberOfArgs
                      | BadReferenceArg
                      | BadArgType
                      | BadReturnType
                      | BadDeclaration
                      | BadIdentifier
                      | BadIfExpression
                      | BadBreak
                      | BadContinue
                      | ReturnNotInFunction deriving Show

type StaticCheckEnv = Map Ident SCType

data SCType = SCInt
            | SCBool
            | SCString
            | SCFun Type [Arg] [Stmt] deriving Eq

typeToSCType :: Type -> SCType
typeToSCType TInt = SCInt
typeToSCType TBool = SCBool
typeToSCType TString = SCString

type StaticCheckMonad = ReaderT (StaticCheckEnv, Bool, Maybe SCType) (ExceptT StaticCheckError IO)

inferType :: Expr -> StaticCheckMonad SCType
inferType ELitTrue = return SCBool

inferType ELitFalse = return SCBool

inferType (ELitInt _) = return SCInt

inferType (EString _) = return SCString

inferType (ENeg expr) = do
  exprType <- inferType expr
  if exprType == SCBool then
    return SCBool
  else
    throwError BadTypeInExpr

inferType (ENot expr) = do
  exprType <- inferType expr
  if exprType == SCInt then
    return SCInt
  else
    throwError BadTypeInExpr

inferType (EMul expr1 _ expr2) = do
  exprType1 <- inferType expr1
  exprType2 <- inferType expr2
  if exprType1 == SCInt && exprType2 == SCInt then
    return SCInt
  else
    throwError BadTypeInExpr

inferType (EAdd expr1 addOp expr2) = do
  exprType1 <- inferType expr1
  exprType2 <- inferType expr2
  if exprType1 == SCInt && exprType2 == SCInt then
    return SCInt
  else if addOp == OpAdd && exprType1 == SCString && exprType2 == SCString then
    return SCString
  else
    throwError BadTypeInExpr

inferType (ERel expr1 relOp expr2) = do
  exprType1 <- inferType expr1
  exprType2 <- inferType expr2
  if exprType1 == exprType2 then
    return SCBool
  else
    throwError BadTypeInExpr

inferType (EAnd expr1 expr2) = do
  exprType1 <- inferType expr1
  exprType2 <- inferType expr2
  if exprType1 == SCBool && exprType2 == SCBool then
    return SCBool
  else
    throwError BadTypeInExpr

inferType (EOr expr1 expr2) = inferType (EAnd expr1 expr2)

inferType (EVar ident) = do
  varType <- getIdentType ident
  case varType of
    SCFun _ _ _ -> throwError BadIdentifier
    _           -> return varType

inferType (EApp ident exprs) = do
  funType <- getIdentType ident
  case funType of
    SCFun retType args _ -> do
      checkArgs args exprs
      return $ typeToSCType retType
    _ -> throwError BadIdentifier

checkArgs :: [Arg] -> [Expr] -> StaticCheckMonad ()
checkArgs ((ArgVal argType _):args) (expr:exprs) = do
  exprType <- inferType expr
  if exprType == typeToSCType argType then
    checkArgs args exprs
  else
    throwError BadArgType
checkArgs ((ArgRef argType argIdent):args) (var@(EVar varIdent):exprs) = do
  exprType <- inferType var
  if exprType == typeToSCType argType then
    checkArgs args exprs
  else
    throwError BadArgType
checkArgs [] [] = return ()
checkArgs [] _ = throwError BadNumberOfArgs
checkArgs _ [] = throwError BadNumberOfArgs
checkArgs _ _ = throwError BadReferenceArg


getIdentType :: Ident -> StaticCheckMonad SCType
getIdentType ident = do
  (env, _, _) <- ask
  case (env !? ident) of
    Nothing -> throwError BadIdentifier
    Just v  -> return v



checkStmt :: Stmt -> StaticCheckMonad StaticCheckEnv
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
      let newEnv = insert ident (typeToSCType varType) env
      local (\(_, isLoop, retType) -> (newEnv, isLoop, retType)) $ checkStmt (VDecl varType items)
    Init ident expr -> do
      exprType <- inferType expr
      let newEnv = insert ident (typeToSCType varType) env
      if exprType == typeToSCType varType then
        local (\(_, isLoop, retType) -> (newEnv, isLoop, retType)) $ checkStmt (VDecl varType items)
      else
        throwError BadDeclaration

checkStmt (Ret expr) = do
  (env, _, retType) <- ask
  exprType <- inferType expr
  if retType == Nothing then
    throwError ReturnNotInFunction
  else if fromJust retType /= exprType then
    throwError BadReturnType
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

checkStmt (SExpr expr) = do
  (env, _, _) <- ask
  inferType expr
  return env

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
  if exprType /= SCBool then
    throwError BadTypeInExpr
  else do
    local (\(_, _, mSCType) -> (env, True, mSCType)) $ checkStmt stmt
    return env

checkStmt (Cond expr stmt) = do
  (env, _, _) <- ask
  exprType <- inferType expr
  if exprType /= SCBool then
    throwError BadIfExpression
  else do
    checkStmt stmt
    return env

checkStmt (CondElse expr stmt1 stmt2) = do
  (env, _, _) <- ask
  exprType <- inferType expr
  if exprType /= SCBool then
    throwError BadIfExpression
  else do
    checkStmt stmt1
    checkStmt stmt2
    return env


-- sprawdzenie bloku statementów pod wprowadzeniem argsów
checkStmt (FDecl funType ident args (Block stmts)) = let
    enrichEnv :: [Arg] -> StaticCheckEnv -> StaticCheckEnv
    enrichEnv [] env = env
    enrichEnv (arg:args) env = case arg of
      (ArgVal argType ident) -> enrichEnv args (insert ident (typeToSCType argType) env)
      (ArgRef argType ident) -> enrichEnv args (insert ident (typeToSCType argType) env)
    enrichEnv2 :: StaticCheckEnv -> StaticCheckEnv
    enrichEnv2 env = insert ident (SCFun funType args stmts) env
  in do
    (env, _, _) <- ask
    local (\_ -> (enrichEnv2 $ enrichEnv args env, False, Just $ typeToSCType funType)) $ checkStmts stmts
    return $ enrichEnv2 env

checkStmt (BStmt (Block stmts)) = do
  (env, _, _) <- ask
  checkStmts stmts
  return env

checkStmts :: [Stmt] -> StaticCheckMonad StaticCheckEnv
checkStmts (stmt:stmts) = do
  (_, isLoop, retType) <- ask
  env <- checkStmt stmt
  -- liftIO $ putStrLn $ show env
  local (const (env, isLoop, retType)) (checkStmts stmts)
checkStmts [] = do
  (env, _, _) <- ask
  return env


staticCheck :: Program -> IO (Either StaticCheckError StaticCheckEnv)
staticCheck (Prog stmts) = runExceptT (runReaderT (checkStmts stmts) (empty, False, Nothing))