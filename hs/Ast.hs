module Ast
( parse
, Ast (Literal, Variable, Sequence)
, Value (IntValue, StrValue, NullValue, BoolValue)
) where

import qualified Sexp

-- Syntax trees.
data Ast
  = Variable Int Value
  | Literal Value
  | Sequence [Ast]
  | AstError Sexp.Sexp
  deriving (Show, Eq)

-- Runtime values.
data Value
  = NullValue
  | BoolValue Bool
  | IntValue Int
  | StrValue [Char]
  deriving (Show, Eq)

-- Parse an s-expression string into a syntax tree.
parse str = adapt (Sexp.parse str)
  where
    adapt (Sexp.IdentSexp stage name) = Variable stage (StrValue name)
    adapt (Sexp.WordSexp "null") = Literal NullValue
    adapt (Sexp.WordSexp "true") = Literal (BoolValue True)
    adapt (Sexp.WordSexp "false") = Literal (BoolValue False)
    adapt (Sexp.IntSexp v) = Literal (IntValue v)
    adapt (Sexp.ListSexp ((Sexp.WordSexp "begin"):rest)) = adaptSequence rest
    adapt e = AstError e
    adaptSequence [] = Literal NullValue
    adaptSequence [e] = adapt e
    adaptSequence elms = Sequence (map adapt elms)
