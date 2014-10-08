module Eval
( eval
, evalFlat
, evalProgram
, evalProgramFlat
, uidStreamStart
, nextUidFromStream
, Result (Normal, Failure)
, FailureCause (UnboundVariable, AbsentNonLocal, CircularReference)
, FlatValue (FlatNull, FlatBool, FlatInt, FlatStr, FlatInstance, FlatHook)
) where

import qualified Value as V
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List
import qualified Data.Maybe as Maybe
import qualified Method as M
import Debug.Trace

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
data PervasiveState hier = PervasiveState {
  -- The uid stream used for generating identity.
  uids :: UidStream,
  -- Object state.
  objects :: Map.Map V.Uid (V.ObjectState hier),
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
genUid s0 = (uid, s1)
  where
    uids0 = uids s0
    (uid, uids1) = nextUidFromStream uids0
    s1 = s0 {uids = uids1}

-- The possible reasons for evaluation to fail.
data FailureCause
  = AbsentNonLocal
  | ExprNotUnderstood V.Expr
  | MethodNotUnderstood [(V.Value, V.Value)]
  | UnboundVariable V.Value
  | UnknownCall V.Value String [V.Value]
  | CircularReference V.Value
  deriving (Show, Eq)

-- The result of an evaluation.
data Result val fail
  = Normal val
  | Failure FailureCause fail
  deriving (Show)

-- A local continuation, the next step during normal evaluation. Continuations
-- always continue in the scope they captured when they were created whereas the
-- pervasive state is always passed in.
type Continuation hier = V.Value -> PervasiveState hier -> Result (V.Value, PervasiveState hier) (PervasiveState hier)

endContinuation v p = Normal (v, p)

-- Dynamically scoped state, that is, state that propagats from caller to
-- callee but not the other way.
data DynamicState hier = DynamicState {
  -- The top nonlocal continuation.
  nonlocal :: V.Uid -> Continuation hier
}

absentNonlocal _ _ p0 = (Failure AbsentNonLocal p0)

-- Initial empty dynamic state.
emptyDynamicState = DynamicState {
  nonlocal = absentNonlocal
}

emptyNamespace = V.Namespace Map.empty

hookScope = Map.fromList (
  [ (V.Str "log", V.Hook V.LogHook)
  , (V.Str "type", V.Hook V.TypeHook)
  ])

-- Initial empty lexical state.
emptyLexicalState methodspace namespace = V.LexicalState {
  V.scope = hookScope,
  V.methodspace = methodspace,
  V.namespace = namespace
}

-- The complete context state at a particular point in the evaluation.
data CompleteState hier = CompleteState {
  lexical :: V.LexicalState hier,
  dynamic :: DynamicState hier,
  pervasive :: PervasiveState hier
}

-- Initial empty version of the complete evaluation state.
emptyCompleteState behavior = CompleteState {
  lexical = emptyLexicalState behavior emptyNamespace,
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
    V.Invoke args
      -> evalInvoke args continue s0
    V.WithEscape name body
      -> evalWithEscape name body continue s0
    V.Ensure body ensure
      -> evalEnsure body ensure continue s0
    _
      -> Failure (ExprNotUnderstood expr) (pervasive s0)

evalVariable name continue s0 =
  if Map.member name scope0
    then continue (scope0 Map.! name) (pervasive s0)
    else evalNamespaceVariable name continue s0
      where
        l0 = lexical s0
        scope0 = V.scope l0

-- Updates the pervasive state of an object, setting its data to the given
-- state.
updateObject p0 uid state = p1
  where
    objects0 = objects p0
    objects1 = Map.insert uid state objects0
    p1 = p0 {objects=objects1}

-- Creates a new object with the given state, returning the object's id and the
-- state that now holds the state.
newObject p0 state = (uid, p2)
  where
    (uid, p1) = genUid p0
    p2 = updateObject p1 uid state

-- Yields the state of the object with the given uid in the given pervasive
-- state.
getObject p0 uid = state
  where
    objects0 = objects p0
    state = objects0 Map.! uid

evalNamespaceVariable name continue s0 = case Map.lookup name refs0 of
  Nothing -> Failure (UnboundVariable name) p0
  Just uid -> getOrCreateBinding uid
  where
    p0 = pervasive s0
    refs0 = V.refs (V.namespace (lexical s0))
    getOrCreateBinding uid = case getObject p0 uid of
      -- If the variable is already bound we simply look it up and continue.
      V.BindingObject (V.Bound value) -> continue value p0
      -- If it's being bound there must have been a cycle.
      V.BindingObject V.BeingBound -> Failure (CircularReference name) p0
      -- If we've not seen it yet it's time to bind it
      V.BindingObject (V.Unbound expr l1) -> createBinding uid expr l1
    createBinding uid value l1 = evalExpr value (thenBind uid) s1
      where
        p1 = updateObject p0 uid (V.BindingObject V.BeingBound)
        d0 = dynamic s0
        s1 = CompleteState {lexical=l1, dynamic=d0, pervasive=p1}
    thenBind uid value p2 = continue value p3
      where
        p3 = updateObject p2 uid (V.BindingObject (V.Bound value))

evalLocalBinding name valueExpr bodyExpr continue s0 = evalExpr valueExpr thenBind s0
  where
    thenBind value p1 = evalExpr bodyExpr continue s1
      where
        l0 = lexical s0
        outerScope = V.scope l0
        innerScope = Map.insert name value outerScope
        l1 = l0 {V.scope = innerScope}
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
evalNewInstance continue s0 = continue (V.Obj uid) p1
  where
    state = V.InstanceObject V.emptyVaporInstanceState
    (uid, p1) = newObject (pervasive s0) state

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
    scope0 = V.scope l0
    scope1 = Map.insert name (V.Hook (V.EscapeHook escapeUid)) scope0
    l1 = l0 {V.scope = scope1}
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

evalInvoke argExprs continue s0 = evalList (map snd argExprs) thenInvoke s0
  where
    l0 = lexical s0
    methodspace0 = V.methodspace l0
    hierarchy0 = V.hierarchy methodspace0
    methods0 = V.methods methodspace0
    thenInvoke argValues p1 = case method of
      Nothing -> Failure (MethodNotUnderstood argList) p1
      Just method -> continue (V.Int 0) p1
      where
        method = M.sigTreeLookup hierarchy0 methods0 argMap
        argList = zip (map fst argExprs) argValues
        argMap = Map.fromList argList

-- Natives
dispatchNative subj = case subj of
  V.Hook V.LogHook -> callLogHookNative subj
  V.Hook (V.EscapeHook _) -> callEscapeHookNative subj
  V.Hook V.TypeHook -> callTypeHookNative subj
  V.Int _ -> callIntNative subj
  _ -> failNative subj

callLogHookNative _ "!" [value] continue s0 = continue value p1
  where
    p0 = pervasive s0
    log0 = valueLog p0
    log1 = log0 ++ [value]
    p1 = p0 {valueLog = log1}
callLogHookNative recv op args continue s0 = failNative recv op args continue s0

callTypeHookNative _ "!" [value] continue s0 = continue result p0
  where
    l0 = lexical s0
    p0 = pervasive s0
    methodspace0 = V.methodspace l0
    hierarchy0 = V.hierarchy methodspace0
    result = V.Obj (M.typeOf hierarchy0 value)
callTypeHookNative _ "display_name" [V.Obj uid] continue s0 = continue displayName p0
  where
    p0 = pervasive s0
    (V.TypeObject state) = (objects p0) Map.! uid
    (V.TypeState displayName) = state
callTypeHookNative recv op args continue s0 = failNative recv op args continue s0

callIntNative (V.Int a) "+" [V.Int b] continue s0 = continue (V.Int (a + b)) (pervasive s0)
callIntNative (V.Int a) "-" [V.Int b] continue s0 = continue (V.Int (a - b)) (pervasive s0)
callIntNative recv op args continue s0 = failNative recv op args continue s0

failNative recv op args _ s0 = Failure (UnknownCall recv op args) (pervasive s0)

-- The set of "magical" root values
data RootValues = RootValues {
  intType :: V.Value,
  strType :: V.Value,
  nullType :: V.Value,
  boolType :: V.Value,
  fallbackType :: V.Value
} deriving (Show)

-- Returns the default root state for the given pervasive state, along with the
-- pervasive state to use from then on.
defaultRootValues p0 = (roots, p5)
  where
    rootType pa0 displayName = (V.Obj uid, pa2)
      where
        state = V.TypeState displayName
        (uid, pa1) = genUid pa0
        objects1 = objects pa1
        objects2 = Map.insert uid (V.TypeObject state) objects1
        pa2 = pa1 {objects = objects2}
    (fallbackType, p1) = rootType p0 V.Null
    (intType, p2) = rootType p1 (V.Str "Integer")
    (strType, p3) = rootType p2 (V.Str "String")
    (nullType, p4) = rootType p3 (V.Str "Null")
    (boolType, p5) = rootType p4 (V.Str "Bool")
    roots = RootValues {
      fallbackType = fallbackType,
      intType = intType,
      strType = strType,
      nullType = nullType,
      boolType = boolType
    }

-- Given a set of roots and a value, returns the type of the value.
typeFromRoots roots value = uid
  where
    (V.Obj uid) = case value of
      V.Int _ -> intType roots
      V.Str _ -> strType roots
      V.Null -> nullType roots
      V.Bool _ -> boolType roots
      _ -> fallbackType roots

-- Default object system
data ObjectSystemState = ObjectSystemState {
  roots :: RootValues,
  inheritance :: Map.Map V.Uid [V.Uid]
}

instance M.TypeHierarchy ObjectSystemState where
  typeOf oss value = typeFromRoots (roots oss) value
  superTypes oss subtype = Map.findWithDefault [] subtype (inheritance oss)

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
  | FlatType V.Uid V.TypeState
  deriving (Show, Eq)

flatten p V.Null = FlatNull
flatten p (V.Bool v) = FlatBool v
flatten p (V.Int v) = FlatInt v
flatten p (V.Str v) = FlatStr v
flatten p (V.Hook v) = FlatHook v
flatten p (V.Obj id) = case state of
  V.InstanceObject state -> FlatInstance id state
  V.TypeObject state -> FlatType id state
  where
    objs = objects p
    state = objs Map.! id

-- Evaluates the given expression, yielding an evaluation result
eval :: (M.TypeHierarchy hier) => V.Methodspace hier -> V.Expr -> Result (V.Value, PervasiveState hier) (PervasiveState hier)
eval methodspace expr = evalExpr expr endContinuation (emptyCompleteState methodspace)

evalFlat :: (M.TypeHierarchy hier) =>  V.Methodspace hier -> V.Expr -> Result (FlatValue, [FlatValue]) [V.Value]
evalFlat behavior expr = case eval behavior expr of
  Normal (value, p0) -> Normal (flatValue, flatLog)
    where
      flatValue = flatten p0 value
      log = valueLog p0
      flatLog = map (flatten p0) log
  Failure cause p0 -> Failure cause (valueLog p0)

-- Given a unified program splits it by stage. The result will be sorted by
-- increasing stage.
splitProgram (V.UnifiedProgram unifiedDecls body) = V.SplitProgram splitDecls body
  where
    stagedDecls = [(stageOf decl, decl) | decl <- unifiedDecls]
    groups = List.groupBy (\ a b -> fst a == fst b) stagedDecls
    splitDecls = [(s, map (toSplit . snd) group) | group@((s, _):_) <- groups]
    stageOf (V.UnifiedNamespaceBinding stage _ _) = stage 
    toSplit (V.UnifiedNamespaceBinding _ name value) = V.SplitNamespaceBinding name value

-- Given a list of split declarations returns a list of (name, value) pairs for
-- all the namespace declarations.
namespaceBindings decls = Maybe.catMaybes (map grabBinding decls)
  where
    grabBinding (V.SplitNamespaceBinding name value) = Just (name, value)

-- Given a list of namespace declarations etc. yields a lexical scope where
-- the namespace declarations have been seeded but not yet evaluated, as well as
-- a new pervasive state.
lexicalForDeclarations decls methodspace0 p0 = (l0, p1)
  where
    namespace0 = V.Namespace refs
    l0 = emptyLexicalState methodspace0 namespace0
    prepareSingleBinding (name, value) pA = (name, uid, pB)
      where
        state = V.BindingObject (V.Unbound value l0)
        (uid, pB) = newObject pA state
    prepareBindings [] (bindings, pA) = (Map.fromList bindings, pA)
    prepareBindings (next:rest) (bindings, pA) = result
      where
        (name, uid, pB) = prepareSingleBinding next pA
        result = prepareBindings rest ((name, uid):bindings, pB)
    (refs, p1) = prepareBindings (namespaceBindings decls) ([], p0)

evalProgram :: V.UnifiedProgram -> Result (V.Value, PervasiveState ObjectSystemState) (PervasiveState ObjectSystemState)
evalProgram unified = runProgram names s2
  where
    (decls, body) = case splitProgram unified of
      V.SplitProgram ((_, decls):_) body -> (decls, body)
      V.SplitProgram [] body -> ([], body)
    -- Start from a completely empty state.
    p0 = emptyPervasiveState
    d0 = emptyDynamicState
    -- Build the roots after which we're in p1.
    (roots, p1) = defaultRootValues p0
    oss = ObjectSystemState roots Map.empty
    methodspace1 = V.Methodspace oss M.emptySigTree
    -- Set up the initial unbound namespace after which we're in p2.
    names = map fst (namespaceBindings decls)
    (l2, p2) = lexicalForDeclarations decls methodspace1 p1
    s2 = CompleteState {lexical = l2, dynamic = d0, pervasive = p2}
    -- Touch all the bindings to ensure they get evaluated and then evaluate
    -- the body.
    runProgram [] sA = evalExpr body endContinuation sA
    runProgram (next:rest) sA = evalNamespaceVariable next thenContinue sA
      where
        thenContinue value pB = runProgram rest (sA {pervasive=pB})

evalProgramFlat :: V.UnifiedProgram -> Result (FlatValue, [FlatValue]) [V.Value]
evalProgramFlat program = case evalProgram program of
  Normal (value, p0) -> Normal (flatValue, flatLog)
    where
      flatValue = flatten p0 value
      log = (valueLog p0)
      flatLog = map (flatten p0) log
  Failure cause p0 -> Failure cause (valueLog p0)
