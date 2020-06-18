--- miCro Tokenizer ---

module miCro_tokenizer where

  open import miCro_parser -- For token data type; parser was written first so it appears in there
  open import miCro
  open import Agda.Builtin.Bool
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl) -- For test programs

  primitive
    primShowChar : Char → String
    primStringFromList : List Char → String

  -- Identifies if a character is a key symbol in miCro, which is to be treated as separate from a word --
  isKeySymbol : Char → Bool
  isKeySymbol '(' = true
  isKeySymbol ')' = true
  isKeySymbol '{' = true
  isKeySymbol '}' = true
  isKeySymbol '[' = true
  isKeySymbol ']' = true
  isKeySymbol ';' = true
  isKeySymbol '+' = true
  isKeySymbol '=' = true
  isKeySymbol '-' = true
  isKeySymbol '*' = true
  isKeySymbol '<' = true
  isKeySymbol '>' = true
  isKeySymbol c = false

  -- Tokenizes a character list. Will remove all whitespace and break symbols into their own string
  -- The second List Char that is passed contains words as they are being read, which is then converted to a string and attached to the tokens once the word's end is reached (with either whitespace or a special symbol
  --Inelegant Solution: key symbol search works on for 1 char, so we do a "manual" search for multi-char symbols first
  --Further inelegant: To avoid stalping empty strings in everywhere, I need a second case for everything where word is empty
  {-# TERMINATING #-}
  token_helper : List Char → List Char → Tokens
  token_helper [] [] = [t]
  token_helper (' ' ∷ chars) [] = token_helper chars []
  token_helper ('\n' ∷ chars) [] = token_helper chars []
  token_helper ('\t' ∷ chars) [] = token_helper chars []
  token_helper ('=' ∷ '='  ∷ chars) [] = ("==" :t: token_helper chars [])
  token_helper ('<' ∷ '='  ∷ chars) [] = ("<=" :t: token_helper chars [])
  token_helper ('>' ∷ '='  ∷ chars) [] = (">=" :t: token_helper chars [])
  token_helper (c ∷ chars) [] with isKeySymbol c
  ... | true = ((primShowChar c) :t: token_helper chars [])
  ... | false = token_helper (c ∷ []) chars
  token_helper [] word = ((primStringFromList word) :t: [t])
  token_helper (' ' ∷ chars) word = ((primStringFromList word) :t: token_helper chars [])
  token_helper ('\n' ∷ chars) word = ((primStringFromList word) :t: token_helper chars [])
  token_helper ('\t' ∷ chars) word = ((primStringFromList word) :t: token_helper chars [])
  token_helper ('=' ∷ '='  ∷ chars) word = ((primStringFromList word) :t: "==" :t: token_helper chars [])
  token_helper ('<' ∷ '='  ∷ chars) word = ((primStringFromList word) :t: "<=" :t: token_helper chars [])
  token_helper ('>' ∷ '='  ∷ chars) word = ((primStringFromList word) :t: ">=" :t: token_helper chars [])
  token_helper (c ∷ chars) word with isKeySymbol c
  ... | true = ((primStringFromList word) :t: (primShowChar c) :t: token_helper chars [])
  ... | false = token_helper (word ++ (c ∷ [])) chars
  

  tokenize : String → Tokens
  tokenize str = token_helper (primStringToList str) []

  charaktar = 'c'
  testC : (primShowChar charaktar) ≡ "c"
  testC = refl

  str = "{x=5}; "
  strt = tokenize str

  test14 : (strt) ≡ ("{" :t: "x" :t: "=" :t: "5" :t: "}" :t: ";" :t: [t])
  test14 = refl
