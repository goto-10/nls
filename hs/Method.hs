module Method
( MatchResult (AnyMatch, EqMatch, NoMatch, IsMatch)
, TypeHierarchy (typeOf, superTypes)
, Guard (Eq, Is, Any)
, matchGuard
) where

import qualified Value as V

-- Parameter guard
data Guard
  = Eq V.Value
  | Is V.Uid
  | Any
  deriving (Show, Eq)

-- The result of matching a guard against a concrete value.
data MatchResult
  = EqMatch
  | IsMatch Int
  | AnyMatch
  | NoMatch
  deriving (Show, Eq, Ord)

-- Provides information about where values fit within the type hierarchy.
class TypeHierarchy a where
  typeOf :: a -> V.Value -> V.Uid
  superTypes :: a -> V.Uid -> [V.Uid]

-- Match a guard against a value in a particular type hierarchy.
matchGuard :: TypeHierarchy a => a -> Guard -> V.Value -> MatchResult
matchGuard _ Any _ = AnyMatch
matchGuard _ (Eq expected) value
    | (expected == value) = EqMatch
    | otherwise = NoMatch
matchGuard hierarchy (Is uid) value = matchIsGuard hierarchy uid 0 valueType
  where
    valueType = typeOf hierarchy value

matchIsGuard hierarchy expected depth found
    | (expected == found) = IsMatch depth
    | otherwise = foldl min NoMatch submatches
      where
        parents = superTypes hierarchy found
        submatches = map (matchIsGuard hierarchy expected (depth + 1)) parents
