module Eval
( eval
, uidStreamStart
, nextUidFromStream
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

-- The state that pervades the entire execution. A change here will be visible
-- across the whole process.
data PervasiveState = PervasiveState {
  uids :: UidStream,
  objects :: Map.Map Uid Int
} deriving (Show)

-- A completely empty pervasive state with no objects or state at all.
emptyPervasiveState = PervasiveState {
  uids = uidStreamStart,
  objects = Map.empty
}

-- Given a pervasive state, returns a fresh object id and a new pervasive state
-- to use from that point on.
genUid state = (uid, newState)
  where
    (uid, newUids) = nextUidFromStream (uids state)
    newState = state { uids = newUids }

eval expr = Ast.NullValue
