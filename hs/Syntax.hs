module Syntax
( classify
, Operator (Infix, Prefix, Suffix, Implicit)
) where

import qualified Data.Maybe as Maybe
import qualified Debug.Trace as Trace

data Operator
  = Infix String
  | Prefix String
  | Suffix String
  | Implicit
  deriving (Show, Eq)

data RelativePrecedence
  = Same
  | Tighter
  | Looser
  | Unrelated

comparePrecedence a b =
  if a < b
    then Tighter
  else if a == b
    then Same
    else Looser

isLooser a b =
  case comparePrecedence a b of
    Looser -> True
    _ -> False

getPrecedence (Infix s) = s
getPrecedence (Prefix s) = s
getPrecedence (Suffix s) = s
getPrecedence Implicit = "n"

-- Given a list of strings returns Just a list of those strings classified as
-- operators if there is a valid classification, otherwise Nothing.
classify [] = Just [Implicit]
classify ops = result
  where
    opCount = length ops
    -- If the classification where the n'th operator is the infix one is valid
    -- then return Just that. If it's invalid return Nothing.
    validCandidate n = result
      where
        suffixes = map Suffix (take n ops)
        infixx = Infix (ops !! n)
        prefixes = map Prefix (drop (n + 1) ops)
        suffixPrecs = map getPrecedence suffixes
        prefixPrecs = map getPrecedence prefixes
        infixPrec = getPrecedence infixx
        suffixComps = map (isLooser infixPrec) suffixPrecs
        prefixComps = map (isLooser infixPrec) prefixPrecs
        isValid = and (suffixComps ++ prefixComps)
        candidate = suffixes ++ [infixx] ++ prefixes
        result = if isValid then (Just candidate) else Nothing
    candidates = [validCandidate pivot | pivot <- [0 .. (opCount - 1)]]
    valids = Maybe.catMaybes candidates
    result = pickUnique valids
    pickUnique [x] = Just x
    pickUnique _ = Nothing
