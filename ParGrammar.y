-- This Happy file was machine-generated by the BNF converter
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module ParGrammar where
import AbsGrammar
import LexGrammar
import ErrM

}

%name pProgram Program
-- no lexer declaration
%monad { Err } { thenM } { returnM }
%tokentype {Token}
%token
  '!' { PT _ (TS _ 1) }
  '!=' { PT _ (TS _ 2) }
  '&&' { PT _ (TS _ 3) }
  '(' { PT _ (TS _ 4) }
  ')' { PT _ (TS _ 5) }
  '*' { PT _ (TS _ 6) }
  '+' { PT _ (TS _ 7) }
  ',' { PT _ (TS _ 8) }
  '-' { PT _ (TS _ 9) }
  '/' { PT _ (TS _ 10) }
  ';' { PT _ (TS _ 11) }
  '<' { PT _ (TS _ 12) }
  '<=' { PT _ (TS _ 13) }
  '=' { PT _ (TS _ 14) }
  '==' { PT _ (TS _ 15) }
  '>' { PT _ (TS _ 16) }
  '>=' { PT _ (TS _ 17) }
  '[' { PT _ (TS _ 18) }
  ']' { PT _ (TS _ 19) }
  'bool' { PT _ (TS _ 20) }
  'break' { PT _ (TS _ 21) }
  'continue' { PT _ (TS _ 22) }
  'else' { PT _ (TS _ 23) }
  'emptyList' { PT _ (TS _ 24) }
  'false' { PT _ (TS _ 25) }
  'fetch' { PT _ (TS _ 26) }
  'get' { PT _ (TS _ 27) }
  'if' { PT _ (TS _ 28) }
  'int' { PT _ (TS _ 29) }
  'length' { PT _ (TS _ 30) }
  'list' { PT _ (TS _ 31) }
  'print' { PT _ (TS _ 32) }
  'ref' { PT _ (TS _ 33) }
  'return' { PT _ (TS _ 34) }
  'string' { PT _ (TS _ 35) }
  'true' { PT _ (TS _ 36) }
  'tuple' { PT _ (TS _ 37) }
  'while' { PT _ (TS _ 38) }
  '{' { PT _ (TS _ 39) }
  '||' { PT _ (TS _ 40) }
  '}' { PT _ (TS _ 41) }

L_ident  { PT _ (TV $$) }
L_integ  { PT _ (TI $$) }
L_quoted { PT _ (TL $$) }


%%

Ident   :: { Ident }   : L_ident  { Ident $1 }
Integer :: { Integer } : L_integ  { (read ( $1)) :: Integer }
String  :: { String }  : L_quoted {  $1 }

Program :: { Program }
Program : ListStmt { AbsGrammar.Prog (reverse $1) }
Type :: { Type }
Type : 'int' { AbsGrammar.TInt }
     | 'bool' { AbsGrammar.TBool }
     | 'string' { AbsGrammar.TString }
     | 'tuple' '<' ListType '>' { AbsGrammar.TTuple $3 }
     | 'list' '<' Type '>' { AbsGrammar.TList $3 }
ListType :: { [Type] }
ListType : Type { (:[]) $1 } | Type ',' ListType { (:) $1 $3 }
Blck :: { Blck }
Blck : '{' ListStmt '}' { AbsGrammar.Block (reverse $2) }
ListStmt :: { [Stmt] }
ListStmt : {- empty -} { [] } | ListStmt Stmt { flip (:) $1 $2 }
Stmt :: { Stmt }
Stmt : ';' { AbsGrammar.Empty }
     | Blck { AbsGrammar.BStmt $1 }
     | Type ListItem ';' { AbsGrammar.VDecl $1 $2 }
     | Type Ident '(' ListArg ')' Blck { AbsGrammar.FDecl $1 $2 $4 $6 }
     | Ident '=' Expr ';' { AbsGrammar.Assign $1 $3 }
     | 'return' Expr ';' { AbsGrammar.Ret $2 }
     | 'continue' ';' { AbsGrammar.Cont }
     | 'break' ';' { AbsGrammar.Break }
     | 'if' '(' Expr ')' Stmt { AbsGrammar.Cond $3 $5 }
     | 'if' '(' Expr ')' Stmt 'else' Stmt { AbsGrammar.CondElse $3 $5 $7 }
     | 'while' '(' Expr ')' Stmt { AbsGrammar.While $3 $5 }
     | 'print' Expr ';' { AbsGrammar.Print $2 }
     | Expr ';' { AbsGrammar.SExpr $1 }
Arg :: { Arg }
Arg : Type Ident { AbsGrammar.ArgVal $1 $2 }
    | Type 'ref' Ident { AbsGrammar.ArgRef $1 $3 }
ListArg :: { [Arg] }
ListArg : {- empty -} { [] }
        | Arg { (:[]) $1 }
        | Arg ',' ListArg { (:) $1 $3 }
Item :: { Item }
Item : Ident { AbsGrammar.NoInit $1 }
     | Ident '=' Expr { AbsGrammar.Init $1 $3 }
ListItem :: { [Item] }
ListItem : Item { (:[]) $1 } | Item ',' ListItem { (:) $1 $3 }
Expr6 :: { Expr }
Expr6 : Ident { AbsGrammar.EVar $1 }
      | Integer { AbsGrammar.ELitInt $1 }
      | 'true' { AbsGrammar.ELitTrue }
      | 'false' { AbsGrammar.ELitFalse }
      | Ident '(' ListExpr ')' { AbsGrammar.EApp $1 $3 }
      | '(' ListExpr ')' { AbsGrammar.ETuple $2 }
      | 'emptyList' '<' Type '>' { AbsGrammar.EEmptyList $3 }
      | '[' ListExpr ']' { AbsGrammar.EList $2 }
      | 'length' '(' Expr ')' { AbsGrammar.ELength $3 }
      | 'fetch' '(' Expr ',' Expr ')' { AbsGrammar.EFetch $3 $5 }
      | 'get' '(' Expr ',' Integer ')' { AbsGrammar.EGet $3 $5 }
      | String { AbsGrammar.EString $1 }
      | '(' Expr ')' { $2 }
Expr5 :: { Expr }
Expr5 : '-' Expr6 { AbsGrammar.ENeg $2 }
      | '!' Expr6 { AbsGrammar.ENot $2 }
      | Expr6 { $1 }
Expr4 :: { Expr }
Expr4 : Expr4 MulOp Expr5 { AbsGrammar.EMul $1 $2 $3 }
      | Expr5 { $1 }
Expr3 :: { Expr }
Expr3 : Expr3 AddOp Expr4 { AbsGrammar.EAdd $1 $2 $3 }
      | Expr4 { $1 }
Expr2 :: { Expr }
Expr2 : Expr2 RelOp Expr3 { AbsGrammar.ERel $1 $2 $3 }
      | Expr3 { $1 }
Expr1 :: { Expr }
Expr1 : Expr2 '&&' Expr1 { AbsGrammar.EAnd $1 $3 } | Expr2 { $1 }
Expr :: { Expr }
Expr : Expr1 '||' Expr { AbsGrammar.EOr $1 $3 } | Expr1 { $1 }
ListExpr :: { [Expr] }
ListExpr : {- empty -} { [] }
         | Expr { (:[]) $1 }
         | Expr ',' ListExpr { (:) $1 $3 }
AddOp :: { AddOp }
AddOp : '+' { AbsGrammar.OpAdd } | '-' { AbsGrammar.OpSub }
MulOp :: { MulOp }
MulOp : '*' { AbsGrammar.OpMul } | '/' { AbsGrammar.OpDiv }
RelOp :: { RelOp }
RelOp : '<' { AbsGrammar.OpLt }
      | '<=' { AbsGrammar.OpLe }
      | '>' { AbsGrammar.OpGt }
      | '>=' { AbsGrammar.OpGe }
      | '==' { AbsGrammar.OpEq }
      | '!=' { AbsGrammar.OpNeq }
{

returnM :: a -> Err a
returnM = return

thenM :: Err a -> (a -> Err b) -> Err b
thenM = (>>=)

happyError :: [Token] -> Err a
happyError ts =
  Bad $ "syntax error at " ++ tokenPos ts ++ 
  case ts of
    [] -> []
    [Err _] -> " due to lexer error"
    _ -> " before " ++ unwords (map (id . prToken) (take 4 ts))

myLexer = tokens
}

