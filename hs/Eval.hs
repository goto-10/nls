module Eval
( eval
, evalFlat
, uidStreamStart
, nextUidFromStream
, Result (Normal, Failure)
, FailureCause (UnboundVariable, AbsentNonLocal)
, FlatValue (FlatNull, FlatBool, FlatInt, FlatStr, FlatInstance, FlatHook)
) where

import qualified Value as V
import qualified Data.Map as Map
import qualified Method as M

-- A stream of ids. 
data UidStream = UidStream Int
  deriving (Show)

-- Returns the next uid from the given stream along with a new stream which is
-- guaranteed to never return the uid just returned.
nextUidFromStream (UidStream n) = (V.Uid n, UidStream (n + 1))

-- Returns a new fresh uid stream.
uidStreamStart = UidStream 0

type ValueLog = [V.Value]

-- The pervasive, non-scoped, state. This flows linearly through the evaluation
-- independent of scope and control flow -- for instance, leaving a scope can
-- restore a previous scope state but nothing can restore a previous pervasive
-- state.
data PervasiveState = PervasiveState {
  -- The uid stream used for generating identity.
  uids :: UidStream,
  -- Object state.
  objects :: Map.Map V.Uid V.ObjectState,
  -- The log used for testing evaluation order.
  valueLog :: ValueLog
} deriving (Show)

-- A completely empty pervasive state with no objects or state at all.
emptyPervasiveState = PervasiveState {
  uids = uidStreamStart,
  objects = Map.empty,
  valueLog = []
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
  | UnknownCall V.Value String [V.Value]
  deriving (Show, Eq)

-- The result of an evaluation.
data Result val fail
  = Normal val
  | Failure FailureCause fail
  deriving (Show)

-- A local continuation, the next step during normal evaluation. Continuations
-- always continue in the scope they captured when they were created whereas the
-- pervasive state is always passed in.
type Continuation = V.Value -> PervasiveState -> Result (V.Value, PervasiveState) PervasiveState

endContinuation v p = Normal (v, p)

-- Dynamically scoped state, that is, state that propagats from caller to
-- callee but not the other way.
data DynamicState = DynamicState {
  -- The top nonlocal continuation.
  nonlocal :: V.Uid -> Continuation
}

absentNonlocal _ _ p0 = (Failure AbsentNonLocal p0)

-- Initial empty dynamic state.
emptyDynamicState = DynamicState {
  nonlocal = absentNonlocal
}

-- Lexically scoped state, that is, state that doesn't propagate from caller to
-- callee nor the other way (unless there is capturing).
data LexicalState = LexicalState {
  scope :: Map.Map V.Value V.Value
}

hookScope = Map.fromList (
  [ (V.Str "log", V.Hook V.LogHook)
  ])

-- Initial empty lexical state.
emptyLexicalState = LexicalState {
  scope = hookScope
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
    V.Literal v
      -> continue v (pervasive s0)
    V.Variable stage name
      -> evalVariable name continue s0
    V.LocalBinding name value body
      -> evalLocalBinding name value body continue s0
    V.Sequence exprs 
      -> evalSequence exprs continue s0
    V.NewInstance 
      -> evalNewInstance continue s0
    V.CallNative subj name args
      -> evalCallNative subj name args continue s0
    V.WithEscape name body
      -> evalWithEscape name body continue s0
    V.Ensure body ensure
      -> evalEnsure body ensure continue s0
    _
      -> Failure (AstNotUnderstood expr) (pervasive s0)

evalVariable name continue s0 =
  if Map.member name vars
    then continue (vars Map.! name) (pervasive s0)
    else Failure (UnboundVariable name) (pervasive s0)
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

-- Evaluates a list of expressions, yielding the value of the last one (or Null
-- if the list is empty.
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

-- Evaluates a list of expressions, yielding a list of their values.
evalList exprs continue s0 = evalListAccum exprs s0 []
  where
    evalListAccum [] s0 accum = continue (reverse accum) (pervasive s0)
    evalListAccum (next:rest) s0 accum = evalExpr next thenRest s0
      where
        thenRest value p1 = evalListAccum rest s1 (value:accum)
          where
            s1 = s0 {pervasive=p1}

evalWithEscape name bodyExpr continue s0 = evalExpr bodyExpr continue s1
  where
    -- Generate a unique id for this escape.
    p0 = pervasive s0
    (escapeUid, p1) = genUid p0
    -- Hook the escape into the chain of nonlocals.
    d0 = dynamic s0
    nonlocal0 = nonlocal d0
    nonlocal1 targetUid
        | targetUid == escapeUid = continue
        | otherwise = nonlocal0 targetUid
    -- Give the escape hook a name in the body's scope.
    l0 = lexical s0
    scope0 = scope l0
    scope1 = Map.insert name (V.Hook (V.EscapeHook escapeUid)) scope0
    l1 = l0 {scope = scope1}
    d1 = d0 {nonlocal = nonlocal1}
    s1 = s0 {lexical = l1, dynamic = d1, pervasive = p1}

callEscapeHookNative (V.Hook (V.EscapeHook uid)) "!" [val] continue s0 = bail val p0
  where
    d0 = dynamic s0
    nonlocal0 = nonlocal d0
    bail = nonlocal0 uid
    p0 = pervasive s0

evalEnsure bodyExpr ensureExpr continue s0 = evalExpr bodyExpr thenEvalEnsure s1
  where
    -- The ensure-block is evaluated in the same dynamic scope as the one in
    -- which it was defined such that if it escapes itself it won't end in an
    -- infinite loop.
    --
    -- After evaluating the ensure block we discard its result and continue
    -- evaluation with the value of the block such that the result value of
    -- the whole thing is unaffected by the ensure block.
    --
    -- The pervasive state is called pa1 to reflect the fact that there are
    -- two paths through this code, the non-escape (a) and escape (b) path.
    thenEvalEnsure bodyValue pa1 = evalExpr ensureExpr thenDiscardValue sa1
      where
        sa1 = s0 {pervasive = pa1}
        thenDiscardValue ensureValue = continue bodyValue
    d0 = dynamic s0
    nonlocal0 = nonlocal d0
    -- If the body escapes we evaluate the ensure block with a continuation
    -- that continues escaping past this escape. As in the normal case the
    -- evaluation of the block happens in the same dynamic scope as the one
    -- in which it is defined, again to avoid looping if it escapes itself.
    nonlocal1 targetUid escapeValue pb1 = evalExpr ensureExpr thenContinueEscape sb1
      where
        sb1 = s0 {pervasive = pb1}
        thenContinueEscape ensureValue = nonlocal0 targetUid escapeValue
    d1 = d0 {nonlocal=nonlocal1}
    s1 = s0 {dynamic=d1}

-- Evaluates a function call expression.
evalCallNative recvExpr name argsExprs continue s0 = evalExpr recvExpr thenArgs s0
  where
    thenArgs recv p1 = evalList argsExprs thenCall s1
      where
        s1 = s0 {pervasive=p1}
        thenCall args p2 = dispatchNative recv name args continue s2
          where
            s2 = s0 {pervasive=p2}

-- Natives
dispatchNative subj = case subj of
  V.Hook V.LogHook -> callLogHookNative subj
  V.Int _ -> callIntNative subj
  V.Hook (V.EscapeHook _) -> callEscapeHookNative subj
  _ -> failNative subj

callLogHookNative _ "!" [value] continue s0 = continue value p1
  where
    p0 = pervasive s0
    log0 = valueLog p0
    log1 = log0 ++ [value]
    p1 = p0 {valueLog = log1}
callLogHookNative recv op args continue s0 = failNative recv op args continue s0

callIntNative (V.Int a) "+" [V.Int b] continue s0 = continue (V.Int (a + b)) (pervasive s0)
callIntNative (V.Int a) "-" [V.Int b] continue s0 = continue (V.Int (a - b)) (pervasive s0)
callIntNative recv op args continue s0 = failNative recv op args continue s0

failNative recv op args _ s0 = Failure (UnknownCall recv op args) (pervasive s0)

-- Flattened runtime values, that is, values where the part that for Values
-- belong in the pervasive state have been extracted and embedded directly in
-- the flat value.
data FlatValue
  = FlatNull
  | FlatBool Bool
  | FlatInt Int
  | FlatStr String
  | FlatHook V.Hook
  | FlatInstance V.Uid V.InstanceState
  deriving (Show, Eq)

flatten p V.Null = FlatNull
flatten p (V.Bool v) = FlatBool v
flatten p (V.Int v) = FlatInt v
flatten p (V.Str v) = FlatStr v
flatten p (V.Hook v) = FlatHook v
flatten p (V.Obj id) = case state of
  V.Instance inst -> FlatInstance id inst
  where
    objs = objects p
    state = objs Map.! id

-- Evaluates the given expression, yielding an evaluation result
eval :: V.Ast -> Result (V.Value, PervasiveState) PervasiveState
eval expr = evalExpr expr endContinuation emptyCompleteState

evalFlat :: V.Ast -> Result (FlatValue, [FlatValue]) [V.Value]
evalFlat expr = case eval expr of
  Normal (value, p0) -> Normal (flatValue, flatLog)
    where
      flatValue = flatten p0 value
      log = (valueLog p0)
      flatLog = map (flatten p0) log
  Failure cause p0 -> Failure cause (valueLog p0)
