module Method
( MatchResult (AnyMatch, EqMatch, NoMatch, IsMatch)
) where

import qualified Value as V

data Guard
  = Eq V.Value
  | Is V.Uid
  | Any
  deriving (Show, Eq)

data Parameter
  = Parameter Guard [V.Value]
  deriving (Show, Eq)

data SigSeg = SigSeg [Parameter]

data Signature = Signature [SigSeg]

data MatchResult
  = EqMatch
  | IsMatch Int
  | AnyMatch
  | NoMatch
  deriving (Show, Eq, Ord)

data Hierarchy = Hierarchy {
  getType :: V.Value -> V.Uid,
  getTypeParents :: V.Uid -> [V.Uid]
}

matchGuard Any _ _ = AnyMatch
matchGuard (Eq expected) value _
    | (expected == value) = EqMatch
    | otherwise = NoMatch
matchGuard (Is uid) value hierarchy = matchIsGuard uid hierarchy 0 valueType
  where
    valueType = (getType hierarchy) value

matchIsGuard expected hierarchy depth found
    | (expected == found) = IsMatch depth
    | otherwise = foldl min NoMatch submatches
      where
        parents = (getTypeParents hierarchy) found
        submatches = map (matchIsGuard expected hierarchy (depth + 1)) parents
