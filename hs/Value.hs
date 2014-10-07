module Value
( parseExpr
, parseProgram
, Expr (Literal, Variable, Sequence, LocalBinding, NewInstance, CallNative, WithEscape, Ensure, Invoke)
, Decl (NamespaceBinding)
, Program (Program)
, Value (Int, Str, Null, Bool, Obj, Hook)
, Hook (LogHook, EscapeHook, TypeHook)
, Phase (Vapor, Fluid, Frozen)
, Uid (Uid)
, ObjectState (InstanceObject, TypeObject, BindingObject)
, InstanceState (InstanceState)
, TypeState (TypeState)
, BindingState (Bound, Unbound, BeingBound)
, Guard (Eq, Is, Any)
, Parameter (Parameter)
, SigTree (SigTree)
, Signature
, Namespace (Namespace)
, Methodspace (Methodspace)
, LexicalState (LexicalState)
, tags
, guard
, emptyVaporInstanceState
, scope
, methodspace
, hierarchy
, methods
, namespace
, refs
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

-- Parameter guard
data Guard
  = Eq Value
  | Is Uid
  | Any
  deriving (Show, Eq)

-- An individual signature parameter
data Parameter = Parameter {
  tags :: [Value],
  guard :: Guard
} deriving (Show, Eq)

-- A full method signature.
type Signature = [Parameter]

-- A signature tree which maps arguments to values through multiple dispatch.
data SigTree a = SigTree (Maybe a) [(Signature, SigTree a)]
  deriving (Show, Eq)

-- The state that gives behavior to objects.
data Methodspace a = Methodspace {
  hierarchy :: a,
  methods :: SigTree Integer
} deriving (Show, Eq)

-- A module namespace. The actual values of the mappings are stored in the
-- pervasive state since they're mutable.
data Namespace = Namespace {
  refs :: Map.Map Value Uid
} deriving (Show, Eq)

-- Lexically scoped state, that is, state that doesn't propagate from caller to
-- callee nor the other way (unless there is capturing).
data LexicalState a = LexicalState {
  scope :: Map.Map Value Value,
  methodspace :: Methodspace a,
  namespace :: Namespace
} deriving (Show, Eq)

-- The mutable (potentially) state of an instance object.
data InstanceState = InstanceState {
  phase :: Phase,
  fields :: Map.Map Uid Value
} deriving (Show, Eq)

-- An empty instance in the vapor state. This is how instances typically start.
emptyVaporInstanceState = InstanceState {
  phase = Vapor,
  fields = Map.empty
}

-- State associated with a type object.
data TypeState = TypeState {
  displayName :: Value
} deriving (Show, Eq)

data BindingState a
  = Bound Value
  | BeingBound
  | Unbound Expr (LexicalState a)
  deriving (Show, Eq)

data ObjectState a
  = InstanceObject InstanceState
  | TypeObject TypeState
  | BindingObject (BindingState a)
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

parseProgram str = adaptProgram (S.parseSexp str)
  where
    adaptProgram (S.List ((S.Word "program"):rest)) = adaptToplevels rest [] nullBody
    adaptToplevels [] decls body = Program decls body
    adaptToplevels (next:rest) decls body = case next of
      S.List [S.Word "do", expr]
        -> adaptToplevels rest decls (adaptExpr expr)
      S.List [S.Word "def", S.Ident 0 name, S.Delim ":=", value]
        -> adaptToplevels rest (decl:decls) body
        where
          decl = NamespaceBinding (Str name) (adaptExpr value)

    nullBody = Literal Null
