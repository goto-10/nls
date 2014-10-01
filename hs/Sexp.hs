module Sexp
( tokenize
, parseSexp
, Token (IdentToken, OpToken, DelimToken, WordToken, IntToken)
, Sexp (Ident, List, Int, Error, Word, Delim, Op)
) where

import Text.Regex

-- S-expression tokens.
data Token
  = IdentToken Int String
  | OpToken String
  | IntToken Int
  | WordToken String
  | DelimToken String
  | ErrorToken String
  deriving (Show, Eq)

-- A list of the regular expressions that describe each token along with the
-- factory function to use to convert a string match to a token.
allTokens =
  [ ("(\\$+|@+)([a-z_]+)", makeIdent)
  , ("\\.([a-z_]+)", makeNamedOp)
  , ("([+<>=:!]+)", makeOperator)
  , ("([a-z_]+)", makeWord)
  , ("([0-9]+)", makeInt)
  , ("([(){}])", makeDelimiter)
  , ("[ \t\r\f\n]", ignoreToken)
  ]
  where
    makeIdent [stage, name] = [IdentToken (countStages stage) name]
      where
        countStages "$" = 0
        countStages ('$':rest) = 1 + (countStages rest)
        countStages "@" = -1
        countStages ('@':rest) = (countStages rest) - 1
    makeNamedOp [name] = [OpToken name]
    makeOperator [":="] = [DelimToken ":="]
    makeOperator [name] = [OpToken name]
    makeDelimiter [value] = [DelimToken value]
    makeWord [word] = [WordToken word]
    makeInt [value] = [IntToken (read value)]
    ignoreToken [] = []

-- The token strings compiled to a regexp, still along with the converter.
allCompiledTokens = [(compileRegex s, f) | (s, f) <- allTokens]
  where compileRegex s = mkRegexWithOpts ("^(" ++ s ++ ")") True False

-- Given a string, returns the first match against a token and the rest of
-- the string, or Nothing if no tokens match the input.
matchNextToken str = findFirstMatch allCompiledTokens
  where
    findFirstMatch [] = Nothing
    findFirstMatch ((re, fact):rest) =
      case matchRegex re str
        of Nothing -> findFirstMatch rest
           Just v -> Just (tokens, strTail)
             where
               matchLength = length (head v)
               strTail = drop matchLength str
               captures = tail v
               tokens = fact captures

-- Given a string tokenizes it into sexp tokens.
tokenize str = accumulateTokens str []
  where
    accumulateTokens "" tokens = (tokens, "")
    accumulateTokens rest tokens =
      case matchNextToken rest
        of Nothing -> (tokens, rest)
           Just (token, tail) -> accumulateTokens tail (tokens ++ token)

data ErrorCause
  = ParseFailed [Token]
  | TokenizeFailed String
  deriving (Show, Eq)

-- A parsed s-expression.
data Sexp
  = Ident Int String
  | Word String
  | Delim String
  | Op String
  | Int Int
  | List [Sexp]
  | Error ErrorCause
  deriving (Show, Eq)

-- Parse a string as an s-expression.
parseSexp str =
  case tokenize str
    of (tokens, []) -> fst (parseTokens tokens)
       (_, rest) -> Error (TokenizeFailed rest)
  where
    parseTokens ((IdentToken stage name):r0) = (Ident stage name, r0)
    parseTokens ((WordToken word):r0) = (Word word, r0)
    parseTokens ((IntToken value):r0) = (Int value, r0)
    parseTokens ((OpToken op):r0) = (Op op, r0)
    parseTokens ((DelimToken "("):r0) = parseList r0 []
    parseTokens ((DelimToken s):r0) = (Delim s, r0)
    parseTokens r0 = (Error (ParseFailed r0), [])
    parseList ((DelimToken ")"):r0) accum = (List (reverse accum), r0)
    parseList r0 accum = case parseTokens r0 of
      (e@(Error _), r1) -> (e, r1)
      (elm, rest) -> parseList rest (elm:accum)
