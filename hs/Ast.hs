module Ast
( parse
, Ast (Literal, Variable, Sequence, LocalBinding)
, Value (IntValue, StrValue, NullValue, BoolValue)
) where

import qualified Sexp as S

-- Syntax trees.
data Ast
  = Variable Int Value
  | LocalBinding Value Ast Ast
  | Literal Value
  | Sequence [Ast]
  | AstError S.Sexp
  deriving (Show, Eq)

-- Runtime values.
data Value
  = NullValue
  | BoolValue Bool
  | IntValue Int
  | StrValue String
  deriving (Show, Eq, Ord)

-- Parse an s-expression string into a syntax tree.
parse str = adapt (S.parse str)
  where
    adapt (S.Ident stage name) = Variable stage (StrValue name)
    adapt (S.List [S.Word "def", S.Ident 0 name, S.Delim ":=", value, S.Word "in", body])
      = LocalBinding (StrValue name) (adapt value) (adapt body)
    adapt (S.Word "null") = Literal NullValue
    adapt (S.Word "true") = Literal (BoolValue True)
    adapt (S.Word "false") = Literal (BoolValue False)
    adapt (S.Int v) = Literal (IntValue v)
    adapt (S.List ((S.Word "begin"):rest)) = adaptSequence rest
    adapt e = AstError e
    adaptSequence [] = Literal NullValue
    adaptSequence [e] = adapt e
    adaptSequence elms = Sequence (map adapt elms)
