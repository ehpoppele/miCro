open import miCro

-- First: Read from file into string --

-- process env = initial environment read from string
-- process prog = instructions read from string
-- run exec env prog, and return (print?) output

-- Tokens and related functions --
-- At this point we assume the input file has been parsed into tokens type
-- Token type is a list of strings with all whitespace removed, separated on special characters
-- So "while" should be one list entry, with the proceeding "(" being it's own, and so on.

module miCro_parser where

  open import Agda.Builtin.Bool

  postulate Char : Set
  {-# BUILTIN CHAR Char #-}
  
  data List {a} (A : Set a) : Set a where
    []  : List A
    _∷_ : (x : A) (xs : List A) → List A
  {-# BUILTIN LIST List #-}
  infixr 5 _∷_

  primitive
    primStringToList : String → List Char
    primIsDigit : Char → Bool
    primCharToNat : Char → Nat

  data Tokens : Set where
    [t] : Tokens
    _:t:_ : String → Tokens → Tokens

  _+t+_ : Tokens → Tokens → Tokens
  [t]       +t+ ys  =  ys
  (x :t: xs) +t+ ys  =  x :t: (xs +t+ ys)

  --- PARSING FUNCTION ---
  --- From this point, we assume that we have a tokens list to work with and now convert that to a stmt type

  -- Helper functions to deal with the token stream : slice, eat, split, search, etc.

  -- sliceTo : takes tokens and a string, returns the leading part of tokens up to and including first instance of said string
  sliceTo : Tokens → String → Tokens
  sliceTo [t] str = [t]
  sliceTo (str1 :t: tkns) str2 with primStringEquality str1 str2
  ... | true = (str1 :t: [t])
  ... | false = str1 :t: (sliceTo tkns str2)

  -- eatTokens : takes tokens and string, returns the part of tokens following (but not including) first instance of said string
  eatTokens : Tokens → String → Tokens
  eatTokens [t] str = [t]
  eatTokens (str1 :t: tkns) str2 with primStringEquality str1 str2
  ... | true = tkns
  ... | false = eatTokens tkns str2

  -- Token Split : Searches for the first instance of the given string not in parentheses in the given token list
  -- Splits the list at that point, and return either left or right half, depending on which function was called
  -- Avoid calling this function with "(" or ")" unless you're careful about removing parens
  {-# TERMINATING #-}
  splitL : Tokens → String → Tokens
  splitR : Tokens → String → Tokens
  
  splitL [t] str = [t]
  splitL ( "(" :t: tkns) str = ((splitL tkns ")" ) +t+ (splitL (splitR tkns ")" ) str))
  splitL (str1 :t: tkns) str2 with primStringEquality str1 str2
  ...                           | true = [t]
  ...                           | false = str1 :t: (splitL tkns str2)

  splitR [t] str = [t]
  splitR ( "(" :t: tkns) str = splitR (splitR tkns ")" ) str
  splitR (str1 :t: tkns) str2 with primStringEquality str1 str2
  ...                           | true = tkns
  ...                           | false = splitR tkns str2

  -- Token Search : searches the tokens for the first instance of given string that is not in parentheses
  -- Returns true if one is found, false otherwise
  {-# TERMINATING #-}
  token_search : Tokens → String → Bool
  token_search [t] str = false
  token_search ("(" :t: tkns) str = token_search (splitR tkns ")" ) str
  token_search (str1 :t: tkns) str2 with primStringEquality str1 str2
  ...                                 | true = true
  ...                                 | false = token_search tkns str2

  -- Comparison Token Search : Searches for one of six comparisons (outside of parentheses) and returns the first found
  -- If things were written properly, the first found should be the only one, and if none is found, then "none" is returned
  {-# TERMINATING #-}
  comp_token_search : Tokens → String
  comp_token_search  [t] = "none"
  comp_token_search ("(" :t: tkns) = comp_token_search (splitR tkns ")" )
  comp_token_search ( "==" :t: tkns) = "=="
  comp_token_search ( "!=" :t: tkns) = ">="
  comp_token_search ( "<=" :t: tkns) = "<="
  comp_token_search ( ">=" :t: tkns) = ">="
  comp_token_search ( "<" :t: tkns) = "<"
  comp_token_search ( ">" :t: tkns) = ">"
  comp_token_search (str :t: tkns) = comp_token_search tkns

  -- Similarly returns the first instance of "+" or "-" if one occurs
  {-# TERMINATING #-}
  pm_search : Tokens → String
  pm_search [t] = "none"
  pm_search ("(" :t: tkns) = pm_search (splitR tkns ")" )
  pm_search ("+" :t: tkns) = "+"
  pm_search ("-" :t: tks) = "-"
  pm_search (str :t: tkns) = pm_search tkns

  {-
  -- Checks if a given character is a digit --
  is_digit : Char → Bool
  is_digit '0' = true
  is_digit '1' = true
  is_digit '2' = true
  is_digit '3' = true
  is_digit '4' = true
  is_digit '5' = true
  is_digit '6' = true
  is_digit '7' = true
  is_digit '8' = true
  is_digit '9' = true
  is_digit c = false
  -}

  -- Checks if a given character list is a number --
  is_number : List Char → Bool
  is_number [] = false
  is_number (c ∷ []) with primIsDigit c
  ... | true = true
  ... | false = false
  is_number (c ∷ chars) with primIsDigit c
  ... | true = is_number chars
  ... | false = false

  -- Converts string to a nat, using arithmetic from miCro file
  str_nat_helper : Nat → List Char → Nat
  str_nat_helper n [] = n 
  str_nat_helper n (m ∷ chars) = (str_nat_helper ((n * 10) + (primCharToNat m)) chars) 

  string_to_nat : String → Nat
  string_to_nat str = str_nat_helper 0 (primStringToList str)

  -- Parsing functions, directly interacting with the stream and parsing it. Split into condition, expression, and statement

  -- Parse functions for Conditions and Expressions, which are handled separately --
  {-# TERMINATING #-}
  parse_exp : Tokens → Exp
  parse_pm : Tokens → Exp
  parse_plus_rest : Exp → Tokens → Exp
  parse_minus_rest : Exp → Tokens → Exp
  parse_mult : Tokens → Exp
  parse_term : Tokens → Exp

  parse_exp tkns = parse_pm tkns
  parse_pm tkns with pm_search tkns
  ... | "+" = parse_plus_rest (parse_mult (splitL tkns "+")) (splitR tkns "+")
  ... | "-" = parse_minus_rest (parse_mult (splitL tkns "-")) (splitR tkns "+")
  ... | none = parse_mult tkns

  parse_plus_rest exp tkns with pm_search tkns
  ... | "+" = parse_plus_rest (plus exp (parse_mult (splitL tkns "+"))) (splitR tkns "+")
  ... | "-" = parse_minus_rest (plus exp (parse_mult (splitL tkns "-"))) (splitR tkns "+")
  ... | none = (plus exp (parse_exp tkns))

  parse_minus_rest exp tkns with pm_search tkns
  ... | "+" = parse_plus_rest (minus exp (parse_mult (splitL tkns "+"))) (splitR tkns "+")
  ... | "-" = parse_minus_rest (minus exp (parse_mult (splitL tkns "-"))) (splitR tkns "+")
  ... | none = (minus exp (parse_exp tkns))

  parse_mult tkns with token_search tkns "*"
  ... | true = times (parse_term (splitL tkns "*")) (parse_term (splitR tkns "*"))
  ... | false = parse_term tkns

  parse_term ( "(" :t: tkns) = parse_exp (splitL tkns ")")
  parse_term (str :t: [t]) with is_number (primStringToList str) -- At this point we should either have a number or a var; otherwise there's been some error
  ... | true = (const (string_to_nat str))
  ... | false = (readVar str) 
  parse_term tkns = (const 404) -- We can't raise an error, but we should never reach here, since this means something went awry. 

  {-# TERMINATING #-} --Note: Will need to add ability to process literal booleans (t/f) later, unless not needed
  parse_condition : Tokens → Cnd
  parse_disjunction : Tokens → Cnd
  parse_conjunction : Tokens → Cnd
  parse_negation : Tokens → Cnd
  parse_comparison : Tokens → Cnd
  parse_parens_cnd : Tokens → Cnd

  parse_condition tkns = parse_disjunction tkns

  parse_disjunction tkns with token_search tkns "or"
  ...                       | true = ((parse_condition (splitL tkns "or")) Or (parse_condition (splitR tkns "or")))
  ...                       | false = parse_conjunction tkns

  parse_conjunction tkns with token_search tkns "and"
  ...                       | true = ((parse_condition (splitL tkns "and")) And (parse_condition (splitR tkns "and")))
  ...                       | false = parse_negation tkns

  parse_negation ("not" :t: tkns) = (Not (parse_condition tkns))
  parse_negation tkns = parse_comparison tkns

  parse_comparison tkns with comp_token_search tkns
  ... | "==" = ((parse_exp (splitL tkns "==")) == (parse_exp (splitR tkns "==")))
  ... | "!=" = ((parse_exp (splitL tkns "!=")) != (parse_exp (splitR tkns "!=")))
  ... | "<=" = ((parse_exp (splitL tkns "<=")) <= (parse_exp (splitR tkns "<=")))
  ... | ">=" = ((parse_exp (splitL tkns ">=")) >= (parse_exp (splitR tkns ">=")))
  ... | "<" = ((parse_exp (splitL tkns "<")) < (parse_exp (splitR tkns "<")))
  ... | ">" = ((parse_exp (splitL tkns ">")) > (parse_exp (splitR tkns ">")))
  ... | none = parse_parens_cnd tkns -- none just as generic pattern here to satisfy agda, although string "none" will be returned in this case

  parse_parens_cnd ( "(" :t: tkns) = parse_condition (splitL tkns ")")
  parse_parens_cnd other = (cndBool false) --Error; this step should never be reached unless program was written wrong. Should raise error here once I find out how/if I can

  -- parse function, the main function to create the program --
  -- skipping read++ for now, since IDK what that even would be in proper code --
  {-# TERMINATING #-}
  parse : Tokens → Stmt
  parse [t] = No-op
  parse ("if" :t: tkns) = Seq (If (parse_condition (sliceTo tkns ")")) (parse (sliceTo tkns ";"))) (parse (eatTokens tkns ";")) --Creates a sequence between the if stmt and the line after; uses prsCnd to get the condition 
  --parse ("ifElse" :t: tkns) =
  --parse ("while" :t: tkns) =
  --parse (str :t: tkns) with --check if it has digits only; treat as int then; otherwise as var
  parse error = No-op
  

--- Extra Notes ---
-- No ++ is allowed, since right now that reads as a plus operator (solution would be to make it process to "++":t:tkns)
-- 
