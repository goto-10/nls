module Sexp
( tokenize
, parse
, Token (IdentToken, OpToken, DelimToken, WordToken, IntToken)
, Sexp (IdentSexp, ListSexp, IntSexp, ParseError, TokenizeError, WordSexp)
) where

import Text.Regex

-- S-expression tokens.
data Token
  = IdentToken (Int, [Char])
  | OpToken [Char]
  | IntToken Int
  | WordToken [Char]
  | DelimToken [Char]
  | ErrorToken [Char]
  deriving (Show, Eq)

-- A list of the regular expressions that describe each token along with the
-- factory function to use to convert a string match to a token.
allTokens =
  [ ("(\\$+|@+)([a-z_]+)", makeIdent)
  , ("\\.([a-z_]+)", makeNamedOp)
  , ("([+<>=:]+)", makeOperator)
  , ("([a-z_]+)", makeWord)
  , ("([0-9]+)", makeInt)
  , ("([(){}])", makeDelimiter)
  , ("[ \t\r\f\n]", ignoreToken)
  ]
  where
    makeIdent [stage, name] = [IdentToken (countStages stage, name)]
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

-- A parsed s-expression.
data Sexp
  = IdentSexp (Int, [Char])
  | WordSexp [Char]
  | IntSexp Int
  | ListSexp [Sexp]
  | ParseError [Token]
  | TokenizeError [Char]
  deriving (Show, Eq)

-- Parse a string as an s-expression.
parse str =
  case tokenize str
    of (tokens, []) -> fst (parseTokens tokens)
       (_, rest) -> TokenizeError rest
  where
    parseTokens ((IdentToken str):r0) = (IdentSexp str, r0)
    parseTokens ((WordToken word):r0) = (WordSexp word, r0)
    parseTokens ((IntToken value):r0) = (IntSexp value, r0)
    parseTokens ((DelimToken "("):r0) = parseList r0 []
    parseTokens e = (ParseError e, [])
    parseList ((DelimToken ")"):r0) accum = (ListSexp (reverse accum), r0)
    parseList r0 accum = parseList r1 (elm:accum)
      where
        (elm, r1) = parseTokens r0

