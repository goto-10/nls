module Value
( parseExpr
, Expr (Literal, Variable, Sequence, LocalBinding, NewInstance, CallNative, WithEscape, Ensure, Invoke)
, Program (Program)
, Value (Int, Str, Null, Bool, Obj, Hook)
, Hook (LogHook, EscapeHook, TypeHook)
, Phase (Vapor, Fluid, Frozen)
, Uid (Uid)
, ObjectState (InstanceObject, TypeObject)
, InstanceState (InstanceState)
, TypeState (TypeState)
, emptyVaporInstanceState
) where

import qualified Sexp as S
import qualified Data.Map as Map

-- Expression syntax trees
data Expr
  = Variable Int Value
  | LocalBinding Value Expr Expr
  | Literal Value
  | Sequence [Expr]
  | NewInstance
  | CallNative Expr String [Expr]
  | Invoke [(Value, Expr)]
  | WithEscape Value Expr
  | Ensure Expr Expr
  | AstError S.Sexp
  deriving (Show, Eq)

-- Toplevel declarations
data Decl
  = NamespaceBinding Value Expr
  deriving (Show, Eq)

data Program = Program {
  decls :: [Decl],
  body :: Expr
}

-- A unique object id.
data Uid
  = Uid Int
  deriving (Show, Eq, Ord)

-- A marker used to identify values that have magical support in the interpreter.
data Hook
  = LogHook
  | EscapeHook Uid
  | TypeHook
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

data TypeState = TypeState {
  displayName :: Value
} deriving (Show, Eq)

data ObjectState
  = InstanceObject InstanceState
  | TypeObject TypeState
  deriving (Show, Eq)

adaptExpr = adapt
  where
    -- Primitive ops
    adapt (S.Word "null") = Literal Null
    adapt (S.Word "true") = Literal (Bool True)
    adapt (S.Word "false") = Literal (Bool False)
    adapt (S.Int v) = Literal (Int v)
    adapt (S.Ident stage name) = Variable stage (Str name)
    adapt (S.List [S.Word "def", S.Ident 0 name, S.Delim ":=", value, S.Word "in", body])
      = LocalBinding (Str name) (adapt value) (adapt body)
    adapt (S.List ((S.Delim ";"):rest)) = adaptSequence rest
    -- Objects
    adapt (S.List [S.Word "new"]) = NewInstance
    -- Natives
    adapt (S.List (S.Op "!":(S.Op op):subj:args)) = CallNative (adapt subj) op (map adapt args)
    adapt (S.List (S.Op "!":subj:args)) = CallNative (adapt subj) "!" (map adapt args)
    -- Invocation
    adapt (S.List ((S.Op op):subj:rest)) = adaptInvocation op subj rest
    -- Escaping
    adapt (S.List [S.Word "with_escape", S.Ident _ name, S.Word "do", body]) =
      WithEscape (Str name) (adapt body)
    adapt (S.List [S.Word "after", body, S.Word "ensure", ensure]) =
      Ensure (adapt body) (adapt ensure)
    adapt e = AstError e
    adaptSequence [] = Literal Null
    adaptSequence [e] = adapt e
    adaptSequence elms = Sequence (map adapt elms)
    adaptInvocation op subj args = Invoke (subjPair:selPair:argPairs)
      where
       subjPair = (Str "subject", adapt subj)
       selPair = (Str "selector", Literal (Str op))
       argPairs = zip (map Int [0..]) (map adapt args)

-- Parse an s-expression string into a syntax tree.
parseExpr str = adaptExpr (S.parseSexp str)
