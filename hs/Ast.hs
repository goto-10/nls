module Ast
( parse
) where

import qualified Sexp

data Ast
  = Variable (Int, [Char])
  | Literal Value
  | AstError Sexp.Sexp
  deriving (Show, Eq)

data Value
  = NullValue
  | BoolValue Bool
  | IntValue Int
  deriving (Show, Eq)

parse str = adapt (Sexp.parse str)
  where
    adapt (Sexp.IdentSexp e) = Variable e
    adapt (Sexp.WordSexp "null") = Literal NullValue
    adapt (Sexp.WordSexp "true") = Literal (BoolValue True)
    adapt (Sexp.WordSexp "false") = Literal (BoolValue False)
    adapt (Sexp.IntSexp v) = Literal (IntValue v)
    adapt e = AstError e

