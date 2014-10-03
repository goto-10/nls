module Method
( Score (ScoreAny, ScoreEq, ScoreNone, ScoreIs)
, TypeHierarchy (typeOf, superTypes)
, Guard (Eq, Is, Any)
, Parameter (Parameter)
, SigTree (SigTree)
, ScoreRecord (ScoreRecord)
, ScoreRecordOrdering (ScoreRecordOrdering)
, matchGuard
, matchSignature
, emptySigTree
, sigTreeLookup
, compareScoreRecords
, sigAssocLookup
) where

import qualified Value as V
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Maybe as Maybe

-- Parameter guard
data Guard
  = Eq V.Value
  | Is V.Uid
  | Any
  deriving (Show, Eq)

-- The result of matching a guard against a concrete value.
data Score
  = ScoreEq      -- An equality guard matched
  | ScoreIs Int  -- An is-guard matched at this inheritance depth
  | ScoreAny     -- An any-guard matched
  | ScoreAbsent  -- There was no parameter that matched this argument
  | ScoreNone    -- The guard didn't match
  deriving (Show, Eq, Ord)

-- Provides information about where values fit within the type hierarchy.
class TypeHierarchy a where
  typeOf :: a -> V.Value -> V.Uid
  superTypes :: a -> V.Uid -> [V.Uid]

-- Match a guard against a value in a particular type hierarchy.
matchGuard :: TypeHierarchy a => a -> Guard -> V.Value -> Score
matchGuard _ Any _ = ScoreAny
matchGuard _ (Eq expected) value
    | (expected == value) = ScoreEq
    | otherwise = ScoreNone
matchGuard hierarchy (Is uid) value = matchIsGuard hierarchy uid 0 valueType
  where
    valueType = typeOf hierarchy value

-- Match an is-guard.
matchIsGuard hierarchy expected depth current
    | (expected == current) = ScoreIs depth
    | otherwise = foldl min ScoreNone supermatches
      where
        supers = superTypes hierarchy current
        supermatches = map (matchIsGuard hierarchy expected (depth + 1)) supers

-- An individual signature parameter
data Parameter = Parameter {
  tags :: [V.Value],
  guard :: Guard
} deriving (Show, Eq)

-- A full method signature.
type Signature = [Parameter]

-- A set of arguments to match against a signature.
type Arguments = Map.Map V.Value V.Value

-- The successful result of matching an invocation against a signature.
data ScoreRecord = ScoreRecord [(V.Value, Score)]
  deriving (Show, Eq)

-- Matches a signature against an invocation within a given hierarchy. If for
-- each signature parameter there is a unique corresponding value in the
-- invocation which parameter's guard matches successfully then the result is
-- Just a list of (tag, score) pairs which matches the signature in order and
-- where the tag identifies the argument that matched. In all other cases the
-- result is Nothing.
--
-- Note that this function is well-defined even if the signature contains
-- multiple parameters that use the same parameter tag, even though that makes
-- the signature invalid.
matchSignature :: TypeHierarchy a => a -> Signature -> Arguments -> Maybe ScoreRecord
matchSignature hierarchy signature arguments
    | tagsHaveUniqueValue = uniqueValueResult
    | otherwise = Nothing
  where
    -- Grab just the tags from the parameters.
    sigTags = map tags signature
    -- For each tag for each parameter, look for it in the invocation.
    maybeTagValues = [[Map.lookup tag arguments | tag <- tags] | tags <- sigTags]
    -- Discard the ones where lookup failed.
    tagValues = map Maybe.catMaybes maybeTagValues
    -- Determine whether each param found exactly one tag in the arguments.
    tagsHaveUniqueValue = all (== 1) (map length tagValues)
    -- Match the values against the guards.
    scores = map matchParameter (zip (concat tagValues) signature)
      where
        matchParameter (arg, param) = matchGuard hierarchy (guard param) arg
    -- Check whether any of the guards didn't match and otherwise zip the scores
    -- together with the corresponding tags.
    worstScore = foldl max ScoreEq scores
    uniqueValueResult = if worstScore == ScoreNone
      then Nothing
      else Just (ScoreRecord (zip matchingTags scores))
    -- Create a list of the tags that matched. Note: this only has a meaningful
    -- value if tagsHaveUniqueValue is True.
    matchingTags = filter isArgument (concat sigTags)
    isArgument tag = Map.member tag arguments

-- The result of comparing two score records.
data ScoreRecordOrdering = ScoreRecordOrdering {
  hasBetter :: Bool,
  hasWorse :: Bool
} deriving (Show, Eq)

-- Given two score records returns the union where for each tag the most
-- specific score is selected, along with an ordering that says how the first
-- argument compared to the second. That is, better means that there was an
-- entry in the first whose score was a more specific match than the second, and
-- worse means one from the first that was less specific than the second. 
compareScoreRecords :: ScoreRecord -> ScoreRecord -> (ScoreRecordOrdering, ScoreRecord)
compareScoreRecords (ScoreRecord as) (ScoreRecord bs) = (ordering, ScoreRecord minRecord)
  where
    aMap = Map.fromList as
    bMap = Map.fromList bs
    -- The result will consider the record entries from both scores, padding
    -- any absent ones with ScoreAbsent.
    allTags = Set.toList (Set.union (Map.keysSet aMap) (Map.keysSet bMap))
    -- The initial result is that they're equal, then we'll look for evidence
    -- that they're not.
    scoreEqual = ScoreRecordOrdering {hasBetter = False, hasWorse = False}
    (ordering, minRecord) = foldr mergeEntryIntoResult (scoreEqual, []) allTags
    mergeEntryIntoResult tag (runningOrder, runningMin)
        | aScore < bScore = (runningOrder {hasBetter = True}, (tag, aScore):runningMin)
        | aScore > bScore = (runningOrder {hasWorse = True}, (tag, bScore):runningMin)
        | otherwise = (runningOrder, (tag, aScore):runningMin) -- aScore == bScore
        where
          aScore = Map.findWithDefault ScoreAbsent tag aMap
          bScore = Map.findWithDefault ScoreAbsent tag bMap

-- An associative array where they keys are signatures.
type SigAssoc a = [(Signature, a)]

data SigAssocLookupResult a
  -- There was one unique best matching result.
  = Unique a
  -- There were several equally good matching results.
  | Multiple [a]
  -- There were multiple results that weren't equivalent without any of then
  -- being the best.
  | Ambiguous
  -- There was not a single match.
  | None

sigAssocLookup hierarchy args assoc = buildResult bestValues isSynthetic
  where
    (bestValues, maxRecord, isSynthetic) = foldr advanceResult ([], ScoreRecord [], False) assoc
    advanceResult (nextSignature, nextValue) (currentResults, currentMax, isSynthetic) =
      case matchSignature hierarchy nextSignature args of
        Nothing -> (currentResults, currentMax, isSynthetic)
        Just nextRecord -> mergeNextRecord nextValue currentResults currentMax isSynthetic nextRecord
    mergeNextRecord nextValue currentResults currentMax isSynthetic nextRecord =
      case (hasBetter, hasWorse) of
        -- Strictly better than anything we've seen so far. Start a new set of
        -- results.
        (True,  False) -> ([nextValue], nextMax, False)
        -- Strictly worse than something we've seen before so just ignore.
        (False, True) -> (currentResults, nextMax, isSynthetic)
        (False, False) -> if isSynthetic
          -- Equal to the current max which is synthetic, so actually better
          -- than any non-synthetic score we've seen so far.
          then ([nextValue], nextMax, False)
          -- Equal to a previous non-synthetic score so add this to the set of
          -- results.
          else (nextValue:currentResults, nextMax, False)
        -- Not strictly better or worse so we've got an ambiguity and the max
        -- no longer matches any actual signature.
        (True,  True) -> ([], nextMax, True)
      where
        (nextOrdering, nextMax) = compareScoreRecords nextRecord currentMax
        ScoreRecordOrdering hasBetter hasWorse = nextOrdering
    buildResult _ True = Ambiguous
    buildResult [] _ = None
    buildResult [value] _ = Unique value
    buildResult values _ = Multiple values



-- sigAssocLookup args assoc = searchThroughAssoc assoc [] 

-- A signature tree which maps arguments to values through multiple dispatch.
data SigTree a = SigTree (Maybe a) [(Signature, SigTree a)]
  deriving (Show)

emptySigTree = SigTree Nothing []

sigTreeLookup hierarchy (SigTree v branches) args
    | Map.null args = v
    | otherwise = deeperResult
  where
    deeperResult = Nothing
