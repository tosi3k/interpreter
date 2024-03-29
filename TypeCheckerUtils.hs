{- utilities for the type checker -}
module TypeCheckerUtils where


import Control.Monad.Except
import Control.Monad.Reader
import Data.Map hiding (map)
import Data.List (intercalate)

import AbsGrammar

{- type of errors that can occur during static program analysis -}
data StaticCheckError = BadTypeInExpr
                      | BadNumberOfArgs
                      | BadReferenceArg
                      | BadArgType MockType MockType
                      | BadReturnType MockType MockType
                      | BadVarDecl Ident MockType MockType
                      | BadIdentifier Ident
                      | ExpressionNotBoolean
                      | BadBreak
                      | BadContinue
                      | ReturnOutsideOfFunction
                      | GetIndexOutOfRange
                      | GetExpressionNotATuple
                      | NoPartialOrderForTuples
                      | LengthArgumentNotAList
                      | NoPartialOrderForLists
                      | FetchFirstArgumentNotAList
                      | FetchSecondArgumentNotAnInt
                      | BraceListCannotBeEmpty

instance Show StaticCheckError where
  show BadTypeInExpr                  = "Unexpected type in expression evaluation"
  show BadNumberOfArgs                = "Incorrect number of arguments in function application"
  show BadReferenceArg                = "Reference function argument not passed as a variable"
  show (BadArgType e a)               = "Incorrect argument type in function application (expected: " ++ show e ++ ", actual: " ++ show a ++ ")"
  show (BadReturnType e a)            = "Return type mismatch (expected: " ++ show e ++ ", actual: " ++ show a ++ ")"
  show (BadVarDecl (Ident ident) e a) = "RHS of variable " ++ ident ++ " declaration is not of type " ++ show e ++ " (actual: " ++ show a ++ ")"
  show (BadIdentifier (Ident ident))  = "Unknown identifier " ++ ident
  show ExpressionNotBoolean           = "Condition expression inside if/while statement is not boolean"
  show BadBreak                       = "\"break\" statement outside of the loop"
  show BadContinue                    = "\"continue\" statement outside of the loop"
  show ReturnOutsideOfFunction        = "\"return\" statement outside of the function declaration"
  show GetIndexOutOfRange             = "'get' index out of range"
  show GetExpressionNotATuple         = "'get' expression not a tuple"
  show NoPartialOrderForTuples        = "Cannot use relational operators other than '==' and '!=' for tuples"
  show LengthArgumentNotAList         = "'length' argument is not a list"
  show NoPartialOrderForLists         = "Cannot use relational operators other than '==' and '!=' for lists"
  show FetchFirstArgumentNotAList     = "'fetch' first argument is not a list"
  show FetchSecondArgumentNotAnInt    = "'fetch' second argument is not an integer"
  show BraceListCannotBeEmpty         = "Cannot use [] as a notation for an empty list; instead use emptyList<T> where T is a concrete type"

{- mock for identifiers type in our language -}
data MockType = MockInt
              | MockBool
              | MockString
              | MockTuple [MockType]
              | MockList MockType
              | MockFun Type [Arg] [Stmt] deriving Eq

instance Show MockType where
  show MockInt               = "int"
  show MockString            = "string"
  show MockBool              = "bool"
  show (MockList mockType)   = "list<" ++ (show mockType) ++ ">"
  show (MockTuple mockTypes) = "tuple<" ++ (intercalate ", " $ map show mockTypes) ++ ">"

typeToMockType :: Type -> MockType
typeToMockType TInt              = MockInt
typeToMockType TBool             = MockBool
typeToMockType TString           = MockString
typeToMockType (TList listType)  = MockList $ typeToMockType listType
typeToMockType (TTuple typeList) = MockTuple $ map typeToMockType typeList

{- environment for type checker holding identifiers defined so far (with their types) -}
type Env = Map Ident MockType

{-
  monad for the context of type checking
  apart from Env, we also hold a binary information if we are inside a loop
  as well as the expected return type (useful during function declaration analysis)
-}
type TypeCheckerMonad = ReaderT (Env, Bool, Maybe MockType) (ExceptT StaticCheckError IO)

{- identifier type accessor -}
getIdentType :: Ident -> TypeCheckerMonad MockType
getIdentType ident = do
  (env, _, _) <- ask
  case (env !? ident) of
    Nothing -> throwError $ BadIdentifier ident
    Just v  -> return v