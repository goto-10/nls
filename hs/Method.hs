module Method
( Score (ScoreAny, ScoreEq, ScoreNone, ScoreIs)
, TypeHierarchy (typeOf, superTypes)
, Guard (Eq, Is, Any)
, Parameter (Parameter)
, matchGuard
, matchSignature
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
  = ScoreEq
  | ScoreIs Int
  | ScoreAny
  | ScoreNone
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
}

-- A full method signature.
type Signature = [Parameter]

-- Complete data about a method invocation.
type Invocation = Map.Map V.Value V.Value

-- The successful result of matching an invocation against a signature.
type SignatureScore = [(V.Value, Score)]

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
matchSignature :: TypeHierarchy a => a -> Signature -> Invocation -> Maybe SignatureScore
matchSignature hierarchy signature invocation
    | tagsHaveUniqueValue = uniqueValueResult
    | otherwise = Nothing
  where
    -- Grab just the tags from the parameters.
    sigTags = map tags signature
    -- For each tag for each parameter, look for it in the invocation.
    maybeTagValues = [[Map.lookup tag invocation | tag <- tags] | tags <- sigTags]
    -- Discard the ones where lookup failed.
    tagValues = map Maybe.catMaybes maybeTagValues
    -- Determine whether each param found exactly one tag in the invocation.
    tagsHaveUniqueValue = all (== 1) (map length tagValues)
    -- Match the values against the guards.
    scores = map matchParameter (zip (concat tagValues) signature)
      where
        matchParameter (value, param) = matchGuard hierarchy (guard param) value
    -- Check whether any of the guards didn't match and otherwise zip the scores
    -- together with the corresponding tags.
    worstScore = foldl max ScoreEq scores
    uniqueValueResult = if worstScore == ScoreNone
      then Nothing
      else Just (zip matchingTags scores)
    -- Create a list of the tags that matched. Note: this only has a meaningful
    -- value if tagsHaveUniqueValue is True.
    matchingTags = filter inInvocation (concat sigTags)
    inInvocation tag = Map.member tag invocation
