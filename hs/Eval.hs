module Eval
( eval
, uidStreamStart
, nextUidFromStream
, Result (Normal, Failure)
, FailureCause (UnboundVariable)
) where

import qualified Ast
import qualified Data.Map as Map

-- A unique object id.
data Uid
  = Uid Int
  deriving (Show, Eq)

-- A stream of ids. 
data UidStream = UidStream Int
  deriving (Show)

-- Returns the next uid from the given stream along with a new stream which is
-- guaranteed to never return the uid just returned.
nextUidFromStream (UidStream n) = (Uid n, UidStream (n + 1))

-- Returns a new fresh uid stream.
uidStreamStart = UidStream 0

-- The pervasive, non-scoped, state. This flows linearly through the evaluation
-- independent of scope and control flow -- for instance, leaving a scope can
-- restore a previous scope state but nothing can restore a previous pervasive
-- state.
data PervasiveState = PervasiveState {
  uids :: UidStream,
  objects :: Map.Map Uid Int
} deriving (Show)

-- A completely empty pervasive state with no objects or state at all.
emptyPervasiveState = PervasiveState {
  -- The uid stream used for generating identity.
  uids = uidStreamStart,
  -- Object state.
  objects = Map.empty
}

-- Given a pervasive state, returns a fresh object id and a new pervasive state
-- to use from that point on.
genUid state = (uid, newState)
  where
    (uid, newUids) = nextUidFromStream (uids state)
    newState = state { uids = newUids }

-- The possible reasons for evaluation to fail.
data FailureCause
  = AbsentNonLocal
  | AstNotUnderstood Ast.Ast
  | UnboundVariable Ast.Value
  deriving (Show, Eq)

-- The result of an evaluation.
data Result
  = Normal Ast.Value PervasiveState
  | Failure FailureCause
  deriving (Show)

-- A local continuation, the next step during normal evaluation. Continuations
-- always continue in the scope they captured when they were created whereas the
-- pervasive state is always passed in.
type Continuation = Ast.Value -> PervasiveState -> Result

endContinuation = Normal

-- Dynamically scoped state, that is, state that propagats from caller to
-- callee but not the other way.
data DynamicState = DynamicState {
  -- The top nonlocal continuation.
  nonlocal :: Uid -> Continuation
}

absentNonlocal _ _ _ = (Failure AbsentNonLocal)

-- Initial empty dynamic state.
emptyDynamicState = DynamicState {
  nonlocal = absentNonlocal
}

-- Lexically scoped state, that is, state that doesn't propagate from caller to
-- callee nor the other way (unless there is capturing).
data LexicalState = LexicalState {
  scope :: Map.Map Ast.Value Ast.Value
}

-- Initial empty lexical state.
emptyLexicalState = LexicalState {
  scope = Map.empty
}

-- The complete context state at a particular point in the evaluation.
data CompleteState = CompleteState {
  lexical :: LexicalState,
  dynamic :: DynamicState,
  pervasive :: PervasiveState
}

-- Initial empty version of the complete evaluation state.
emptyCompleteState = CompleteState {
  lexical = emptyLexicalState,
  dynamic = emptyDynamicState,
  pervasive = emptyPervasiveState
}

evalExpr expr continue s0 =
  case expr of
    Ast.Literal v -> continue v (pervasive s0)
    Ast.Variable stage name -> evalVariable name continue s0
    Ast.LocalBinding name value body -> evalLocalBinding name value body continue s0
    Ast.Sequence exprs -> evalSequence exprs continue s0
    _ -> Failure (AstNotUnderstood expr)

evalVariable name continue s0 =
  if Map.member name vars
    then continue (vars Map.! name) (pervasive s0)
    else Failure (UnboundVariable name)
  where vars = scope (lexical s0)

evalLocalBinding name valueExpr bodyExpr continue s0 = evalExpr valueExpr thenBind s0
  where
    thenBind value p1 = evalExpr bodyExpr continue s1
      where
        l0 = lexical s0
        outerScope = scope l0
        innerScope = Map.insert name value outerScope
        l1 = l0 {scope = innerScope}
        s1 = s0 {lexical = l1, pervasive = p1}

evalSequence [] continue s0 = continue Ast.NullValue (pervasive s0)
evalSequence [last] continue s0 = evalExpr last continue s0
evalSequence (next:rest) continue s0 = evalExpr next thenRest s0
  where
    thenRest _ p1 = evalSequence rest continue (s0 {pervasive = p1})

-- Evaluates the given expression, yielding an evaluation result
eval :: Ast.Ast -> Result
eval expr = evalExpr expr endContinuation emptyCompleteState
