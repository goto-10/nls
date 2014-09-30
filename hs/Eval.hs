module Eval
( eval
, evalFlat
, uidStreamStart
, nextUidFromStream
, Result (Normal, Failure)
, FailureCause (UnboundVariable)
, FlatValue (FlatNull, FlatBool, FlatInt, FlatStr, FlatInstance)
) where

import qualified Value as V
import qualified Data.Map as Map

-- A stream of ids. 
data UidStream = UidStream Int
  deriving (Show)

-- Returns the next uid from the given stream along with a new stream which is
-- guaranteed to never return the uid just returned.
nextUidFromStream (UidStream n) = (V.Uid n, UidStream (n + 1))

-- Returns a new fresh uid stream.
uidStreamStart = UidStream 0

-- The pervasive, non-scoped, state. This flows linearly through the evaluation
-- independent of scope and control flow -- for instance, leaving a scope can
-- restore a previous scope state but nothing can restore a previous pervasive
-- state.
data PervasiveState = PervasiveState {
  uids :: UidStream,
  objects :: Map.Map V.Uid V.ObjectState
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
  | AstNotUnderstood V.Ast
  | UnboundVariable V.Value
  deriving (Show, Eq)

-- The result of an evaluation.
data Result a
  = Normal a
  | Failure FailureCause
  deriving (Show)

-- A local continuation, the next step during normal evaluation. Continuations
-- always continue in the scope they captured when they were created whereas the
-- pervasive state is always passed in.
type Continuation = V.Value -> PervasiveState -> Result (V.Value, PervasiveState)

endContinuation v p = Normal (v, p)

-- Dynamically scoped state, that is, state that propagats from caller to
-- callee but not the other way.
data DynamicState = DynamicState {
  -- The top nonlocal continuation.
  nonlocal :: V.Uid -> Continuation
}

absentNonlocal _ _ _ = (Failure AbsentNonLocal)

-- Initial empty dynamic state.
emptyDynamicState = DynamicState {
  nonlocal = absentNonlocal
}

-- Lexically scoped state, that is, state that doesn't propagate from caller to
-- callee nor the other way (unless there is capturing).
data LexicalState = LexicalState {
  scope :: Map.Map V.Value V.Value
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
    V.Literal v -> continue v (pervasive s0)
    V.Variable stage name -> evalVariable name continue s0
    V.LocalBinding name value body -> evalLocalBinding name value body continue s0
    V.Sequence exprs -> evalSequence exprs continue s0
    V.NewInstance -> evalNewInstance continue s0
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

evalSequence [] continue s0 = continue V.Null (pervasive s0)
evalSequence [last] continue s0 = evalExpr last continue s0
evalSequence (next:rest) continue s0 = evalExpr next thenRest s0
  where
    thenRest _ p1 = evalSequence rest continue s1
      where
        s1 = s0 {pervasive = p1}

-- Creates a new empty instance.
evalNewInstance continue s0 = continue (V.Obj uid) p2
  where
    (uid, p1) = genUid (pervasive s0)
    state = V.emptyVaporInstanceState
    oldObjects = objects p1
    newObjects = Map.insert uid (V.Instance state) oldObjects
    p2 = p1 { objects = newObjects }

-- Flattened runtime values, that is, values where the part that for Values
-- belong in the pervasive state have been extracted and embedded directly in
-- the flat value.
data FlatValue
  = FlatNull
  | FlatBool Bool
  | FlatInt Int
  | FlatStr String
  | FlatInstance V.Uid V.InstanceState
  deriving (Show, Eq)

flatten V.Null p = FlatNull
flatten (V.Bool v) p = FlatBool v
flatten (V.Int v) p = FlatInt v
flatten (V.Str v) p = FlatStr v
flatten (V.Obj id) p = case state of
  V.Instance inst -> FlatInstance id inst
  where
    objs = objects p
    state = objs Map.! id

-- Evaluates the given expression, yielding an evaluation result
eval :: V.Ast -> Result (V.Value, PervasiveState)
eval expr = evalExpr expr endContinuation emptyCompleteState

evalFlat :: V.Ast -> Result FlatValue
evalFlat expr = case eval expr of
  Normal (v, p) -> Normal (flatten v p)
  Failure c -> Failure c
