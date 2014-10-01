module Value
( parseAst
, Ast (Literal, Variable, Sequence, LocalBinding, NewInstance, Call)
, Value (Int, Str, Null, Bool, Obj, Hook)
, Hook (LogHook)
, Phase (Vapor, Fluid, Frozen)
, Uid (Uid)
, ObjectState (Instance)
, InstanceState (InstanceState)
, emptyVaporInstanceState
) where

import qualified Sexp as S
import qualified Data.Map as Map

-- Syntax trees.
data Ast
  = Variable Int Value
  | LocalBinding Value Ast Ast
  | Literal Value
  | Sequence [Ast]
  | NewInstance
  | Call Ast [Ast]
  | AstError S.Sexp
  deriving (Show, Eq)

-- A unique object id.
data Uid
  = Uid Int
  deriving (Show, Eq, Ord)

data Hook
  = LogHook
  deriving (Show, Eq, Ord)

-- Runtime values. A general value can't be interpreted independently since part
-- of the state is stored in the pervasive state.
data Value
  = Null
  | Bool Bool
  | Int Int
  | Str String
  | Obj Uid
  | Hook Hook
  deriving (Show, Eq, Ord)

-- The phase state of an object.
data Phase
  = Vapor
  | Fluid
  | Frozen
  deriving (Show, Eq)

-- The mutable (potentially) state of an instance object.
data InstanceState = InstanceState {
  phase :: Phase,
  fields :: Map.Map Uid Value
} deriving (Show, Eq)

emptyVaporInstanceState = InstanceState {
  phase = Vapor,
  fields = Map.empty
}

data ObjectState
  = Instance InstanceState
  deriving (Show, Eq)

-- Parse an s-expression string into a syntax tree.
parseAst str = adapt (S.parseSexp str)
  where
    -- Primitive ops
    adapt (S.Word "null") = Literal Null
    adapt (S.Word "true") = Literal (Bool True)
    adapt (S.Word "false") = Literal (Bool False)
    adapt (S.Int v) = Literal (Int v)
    adapt (S.Ident stage name) = Variable stage (Str name)
    adapt (S.List [S.Word "def", S.Ident 0 name, S.Delim ":=", value, S.Word "in", body])
      = LocalBinding (Str name) (adapt value) (adapt body)
    adapt (S.List ((S.Word "begin"):rest)) = adaptSequence rest
    -- Objects
    adapt (S.List [S.Word "new"]) = NewInstance
    adapt (S.List (S.Op "!":subj:args)) = Call (adapt subj) (map adapt args)
    adapt e = AstError e
    adaptSequence [] = Literal Null
    adaptSequence [e] = adapt e
    adaptSequence elms = Sequence (map adapt elms)
