-- First: Read from file into string --

-- process env = initial environment read from string
-- process prog = instructions read from string
-- run exec env prog, and return (print?) output

-- Tokens and related functions --
-- At this point we assume the input file has been parsed into tokens type
-- Token type is a list of strings with all whitespace removed, separated on special characters
-- So "while" should be one list entry, with the proceeding "(" being it's own, and so on.

module miCro_parser where

  open import miCro

  -- Builtins and Primitives --
  open import Agda.Builtin.Bool

  postulate Char : Set
  {-# BUILTIN CHAR Char #-}
  
  data List {a} (A : Set a) : Set a where
    []  : List A
    _∷_ : (x : A) (xs : List A) → List A
  {-# BUILTIN LIST List #-}
  infixr 5 _∷_

  -- List Append
  infixr 5 _++_
  _++_ : ∀ {A : Set} → List A → List A → List A
  []       ++ ys  =  ys
  (x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)
  
  primitive
    primStringToList : String → List Char
    primIsDigit : Char → Bool
    primCharToNat : Char → Nat

  -- Token type, works as a list of strings --
  data Tokens : Set where
    [t] : Tokens
    _:t:_ : String → Tokens → Tokens
  infixr 5 _:t:_

  -- Token append --
  _+t+_ : Tokens → Tokens → Tokens
  [t]       +t+ ys  =  ys
  (x :t: xs) +t+ ys  =  x :t: (xs +t+ ys)

  -- Option and pair types, used with tokens for parse return
  data Option {a} (A : Set a) : Set a where
    None : Option A
    Some : A → Option A

  -- Can use Pair.fst on a pair type to get back the first etc.
  -- Construct with a × b i hope
  record Pair (A B : Set) : Set where
    constructor _×_
    field
      fst : A
      snd : B

  --- PARSING FUNCTIONS ---

  -- Token Split : Searches for the first instance of the given string not in parentheses in the given token list
  -- Splits the list at that point, and return either left or right half, depending on which function was called
  -- Avoid calling this function with "(" or ")" unless you're careful about removing parens
  stopper : Tokens → Bool
  stopper [t] = true
  stopper ("}" :t: tkns) = true
  stopper tkns = false

  -- Removes the given string from the front of tokens. Gives back an empty token list if the string was not found at the front
  eat : Tokens → String → Tokens
  eat (s1 :t: tkns) s2 with primStringEquality s1 s2
  ... | false = [t]
  ... | true = tkns

  -- Returns the first token as a name (could add checking to confirm it isn't a number/doesn't use a unallowed symbol)
  eatName : Tokens → String
  eatName [t] = [t]
  eatName (s :t: tkns) = s
  
  {-# TERMINATING #-}
  splitL : Tokens → String → Tokens
  splitR : Tokens → String → Tokens
  
  splitL [t] str = [t]
  splitL ( "(" :t: tkns) str = "(" :t: ((splitL tkns ")" ) +t+ (")" :t: (splitL (splitR tkns ")" ) str)))
  splitL ( "{" :t: tkns) str = "{" :t: ((splitL tkns "}" ) +t+ ("}" :t: (splitL (splitR tkns "}" ) str)))
  splitL ( "[" :t: tkns) str = "[" :t: ((splitL tkns "]" ) +t+ ("]" :t: (splitL (splitR tkns "]" ) str)))
  splitL (str1 :t: tkns) str2 with primStringEquality str1 str2
  ...                           | true = [t]
  ...                           | false = str1 :t: (splitL tkns str2)

  splitR [t] str = [t]
  splitR ( "(" :t: tkns) str = splitR (splitR tkns ")" ) str
  splitR ( "{" :t: tkns) str = splitR (splitR tkns "}" ) str
  splitR ( "[" :t: tkns) str = splitR (splitR tkns "]" ) str
  splitR (str1 :t: tkns) str2 with primStringEquality str1 str2
  ...                           | true = tkns
  ...                           | false = splitR tkns str2

  --And another helper function for curly brackets, since split needs to treat them like parens but we can't remove them as easily (since we use "(" :t: tkns and cant do "(" tkns "{" etc)
  trimTo : Tokens → String → Tokens
  trimTo [t] str = [t]
  trimTo (str1 :t: tkns) str2 with primStringEquality str1 str2
  ... | true = tkns
  ... | false = trimTo tkns str2

  -- Token Search : searches the tokens for the first instance of given string that is not in parentheses/brackets/braces
  -- Returns true if one is found, false otherwise
  {-# TERMINATING #-}
  token_search : Tokens → String → Bool
  token_search [t] str = false
  token_search ("(" :t: tkns) str = token_search (splitR tkns ")" ) str
  token_search ("{" :t: tkns) str = token_search (splitR tkns "}" ) str
  token_search ("[" :t: tkns) str = token_search (splitR tkns "]" ) str
  token_search (str1 :t: tkns) str2 with primStringEquality str1 str2
  ...                                 | true = true
  ...                                 | false = token_search tkns str2

  -- Comparison Token Search : Searches for one of six comparisons (outside of parentheses) and returns the first found
  -- If things were written properly, the first found should be the only one, and if none is found, then "none" is returned
  {-# TERMINATING #-}
  comp_token_search : Tokens → String
  comp_token_search  [t] = "none"
  comp_token_search ("(" :t: tkns) = comp_token_search (splitR tkns ")" )
  comp_token_search ("{" :t: tkns) = comp_token_search (splitR tkns "}" )
  comp_token_search ("[" :t: tkns) = comp_token_search (splitR tkns "]" )
  comp_token_search ( "==" :t: tkns) = "=="
  comp_token_search ( "!=" :t: tkns) = ">="
  comp_token_search ( "<=" :t: tkns) = "<="
  comp_token_search ( ">=" :t: tkns) = ">="
  comp_token_search ( "<" :t: tkns) = "<"
  comp_token_search ( ">" :t: tkns) = ">"
  comp_token_search (str :t: tkns) = comp_token_search tkns

  -- Plus/Minus search: Similarly returns the first instance of "+" or "-" if one occurs
  {-# TERMINATING #-}
  pm_search : Tokens → String
  pm_search [t] = "none"
  pm_search ("(" :t: tkns) = pm_search (splitR tkns ")" )
  pm_search ("{" :t: tkns) = pm_search (splitR tkns "}" )
  pm_search ("[" :t: tkns) = pm_search (splitR tkns "]" )
  pm_search ("+" :t: tkns) = "+"
  pm_search ("-" :t: tks) = "-"
  pm_search (str :t: tkns) = pm_search tkns

  -- Checks if a given character list is a number --
  isNumber : List Char → Bool
  isNumber [] = false
  isNumber (c ∷ []) with primIsDigit c
  ... | true = true
  ... | false = false
  isNumber (c ∷ chars) with primIsDigit c
  ... | true = isNumber chars
  ... | false = false

  -- Converts string to a nat, using arithmetic from miCro file
  strNatHelper : Nat → List Char → Nat
  strNatHelper n [] = n 
  strNatHelper n (m ∷ chars) = (strNatHelper ((n * 10) + ((primCharToNat m) - 48)) chars) 

  -- Please don't call this on non-numbers
  stringToNat : String → Nat
  stringToNat str = strNatHelper 0 (primStringToList str)

  -- Parsing functions, directly interacting with the stream and parsing it. Split into condition, expression, and statement

  -- Parse functions for Conditions and Expressions, which are handled separately --
  {-# TERMINATING #-}
  parseExp : Tokens → (Option (Pair Tokens Exp))
  parseSum : Tokens → (Option (Pair Tokens Exp))
  parseMult : Tokens → (Option (Pair Tokens Exp))
  parseRestOfSum : Tokens → (Option (Pair Tokens Exp))
  parseRestOfMult : Tokens → (Option (Pair Tokens Exp))
  parseRead : Tokens → (Option (Pair Tokens Exp))
  parseAtom : Tokens → (Option (Pair Tokens Exp))

  parseExp [t] = None -- need to make sure this works
  parseExp tkns = parseSum tkns

  parseSum tkns with parseMult tkns
  ... | None = None
  ... | Some (t × e) = parseRestOfSum e t

  parseRestOfSum e ("+" :t: tkns) with parseMult tkns
  ... | None = None
  ... | Some (t × e2) = parseRestOfSum (plus e e2) t
  parseRestOfSum e ("-" :t: tkns) with parseMult tkns
  ... | None = None
  ... | Some (t × e2) = parseRestOfSum (minus e e2) t
  parseRestOfSum e tkns = Some (tkns × e)

  parseMult tkns with parseRead tkns
  ... | None = None
  ... | Some (t × e) = parseRestOfMult e t

  parseRestOfMult e ("*" :t: tkns) with parseRead tkns
  ... | None = None
  ... | Some (t × e2) = parseRestOfMult (times e e2) t
  parseRestOfMult e tkns = Some (tkns × e)

  parseRead ("&" :t: tkns) with parseAtom tkns
  ... | None = None
  ... | Some (t × e) = Some (t × (readAddress e))

  parseAtom ("[" :t: tkns) with parseExp tkns
  ... | None = None
  ... | Some (t × e) = Some ((eat t "]") × e)
  parseAtom (str :t: tkns) with isNumber (primStringToList str)
  ... | true = Some (tkns × (const (stringToNat str)))
  ... | false = Some (tkns × (readVar str))
  parseAtom [t] = None --I think, might change later

  {-# TERMINATING #-} --Note: Will need to add ability to process literal booleans (t/f) later, unless not needed
  parseCnd : Tokens → Option (Pair Tokens Cnd)

  parseCnd [t] = None
  parseCnd tkns = parseDisj tkns

  parseDisj tkns with parseConj tkns
  ... | None = None
  ... | Some (t × c) = parseRestOfDisj c t

  parseRestOfDisj c ("or" :t: tkns) with parseConj tkns
  ... | None = None
  ... | Some (t × c2) = parseRestOfDisj (c Or c2)
  parseRestOfDisj c tkns = Some (tkns × c)

  parseConj tkns with parseNeg tkns
  ... | None = None
  ... | Some (t × c) = parseRestOfConj

  parseRestOfConj c ("or" :t: tkns) with parseNeg tkns
  ... | None = None
  ... | Some (t × c2) = parseRestOfConj (c And c2)
  parseRestOfConj c tkns = Some (tkns × c)

  parseNeg ("not" :t: tkns) with parseComparison tkns
  ... | None = None
  ... | Some (t × c) = Some (t × (Not c))
  parseNeg tkns = parseComparison tkns

  parseComparison with parseExp tkns
  ... | None = parseBaseCnd tkns
  ... | Some (t × e) = parseRestOfComparison e t

  parseRestOfComparison e ("==" :t: tkns) with parseExp tkns
  ... | None = None
  ... | Some (t × e2) = Some (t × (e == e2))
  -- Rest should be filled out likewise

  parseBaseCnd ("(" :t: tkns) with parseCnd tkns
  ... | None = None
  ... | Some (t × c) = Some ((eat t ")") × c)
  parseBaseCnd ("true" :t: tkns) = Some (tkns × (cndBool true))
  parseBaseCnd ("false" :t: tkns) = Some (tkns × (cndBool false))
  parseBaseCnd other = None --shouldn't be anything else here that could be correct

  parse_condition : Tokens → Cnd
  parse_disjunction : Tokens → Cnd
  parse_conjunction : Tokens → Cnd
  parse_negation : Tokens → Cnd
  parse_comparison : Tokens → Cnd
  parse_literal : Tokens → Cnd
  parse_parens_cnd : Tokens → Cnd

  parse_condition tkns = parse_disjunction tkns

  parse_disjunction tkns with token_search tkns "or"
  ...                       | true = ((parse_conjunction (splitL tkns "or")) Or (parse_disjunction (splitR tkns "or")))
  ...                       | false = parse_conjunction tkns

  parse_conjunction tkns with token_search tkns "and"
  ...                       | true = ((parse_negation (splitL tkns "and")) And (parse_conjunction (splitR tkns "and")))
  ...                       | false = parse_negation tkns

  parse_negation ("not" :t: tkns) = (Not (parse_negation tkns))
  parse_negation tkns = parse_comparison tkns

  parse_comparison tkns with comp_token_search tkns
  ... | "==" = ((parse_exp (splitL tkns "==")) == (parse_exp (splitR tkns "==")))
  ... | "!=" = ((parse_exp (splitL tkns "!=")) != (parse_exp (splitR tkns "!=")))
  ... | "<=" = ((parse_exp (splitL tkns "<=")) <= (parse_exp (splitR tkns "<=")))
  ... | ">=" = ((parse_exp (splitL tkns ">=")) >= (parse_exp (splitR tkns ">=")))
  ... | "<" = ((parse_exp (splitL tkns "<")) < (parse_exp (splitR tkns "<")))
  ... | ">" = ((parse_exp (splitL tkns ">")) > (parse_exp (splitR tkns ">")))
  ... | none = parse_literal tkns -- none just as generic pattern here to satisfy agda, although string "none" will be returned in this case

  parse_literal ("true" :t: [t]) = (cndBool true)
  parse_literal ("false" :t: [t]) = (cndBool false)
  parse_literal tkns = parse_parens_cnd tkns

  parse_parens_cnd ( "(" :t: tkns) = parse_condition (splitL tkns ")")
  parse_parens_cnd other = (cndBool false) --Error; this step should never be reached unless program was written wrong. Should raise error here once I find out how/if I can

  -- Statement parse functions --
  {-# TERMINATING #-}
  parseStmt1 : Tokens → (Option (Pair Tokens Stmt))
  parseStmt2 : (Option (Pair Tokens Stmt)) → (Option (Pair Tokens Stmt))
  parseSingleStmt : Tokens → (Option (Pair Tokens Stmt))
  parseRestOfWhile : Tokens → (Option (Pair Tokens Stmt))
  parseRestOfIf : Tokens → (Option (Pair Tokens Stmt))
  parseRestOfIfElse : Tokens → (Option (Pair Tokens Stmt))
  parseRestOfWrite : Tokens → (Option (Pair Tokens Stmt))

  -- Main Stmt parser; this continually creates a sequence of parsed stmts 
  parseStmt1 [t] = None
  parseStmt1 tkns = parseStmt2 (parseSingleStmt tkns)

  -- Helper function for Stmt1; if these combined I would have to write out parseStmt3 tkns about five times (since I can't use "with" in a "let ... in"), which would mean five times slower parsing
  parseStmt2 None = None
  parseStmt2 (Some (t × s)) with stopper t
  ... | true = (Some ([t] × s))
  ... | false = (Some ([t] × (Seq s (parseStmt1 t))))

  -- Parses a single statement from the tokens; does the "heavy lifting" stmt parsing
  parseSingleStmt [t] = (Some ([t] × No-op)) -- don't know if I need this, but just want to catch errors
  parseSingleStmt ("while" :t: tkns) with (parseCnd (eat tkns "("))
  ... | None = None
  ... | Some (tkns2 × c) = parseRestOfWhile c (eat (eat tkns2 ")") "{")
  parseSingleStmt ("if" :t: tkns) with (parseCnd (eat tkns "("))
  ... | None = None
  ... | Some (tkns2 × c) = parseRestOfIf c (eat (eat tkns2 ")") "{")
  parseSingleStmt ("*" :t: tkns) with parseExp (eat (eat tkns (eatName tkns)) "=") -- A little cheaty since this sort of looks two tokens ahead
  ... | None = None
  ... | Some (tkns2 × e) = Some ((eat tkns2 ";") × (AssignPtr (eatName tkns) e))
  parseSingleStmt ("&" :t: tkns) with parseExp tkns
  ... | None = None
  ... | Some (t × e) = parseRestOfWrite e (eat tkns "=")
  parseSingleStmt tkns with parseExp (eat (eat tkns (eatName tkns)) "=") --This will catch any other errors, as eat will return [t] if it can't eat the expeted token, leading to parseExp returning None
  ... | None = None
  ... | Some (tkns2 × e) = Some ((eat tkns2 ";") × (AssignVar (eatName tkns) e))

  -- Parses the rest of a multi-part statement
  
  parseRestOfWhile c tkns with parseStmt1 tkns
  ... | None = None
  ... | Some (t × s) = Some ((eat t "}") × (While c s))

  parseRestOfIf c tkns with parseStmt1 tkns
  ... | None = None
  ... | Some (t × s) = parseRestOfIfElse c s (eat tkns "}")

  parseRestOfIfElse c s ("else" :t: tkns) with parseStmt1 (eat tkns "{")
  ... | None = None
  ... | Some (t × s2) = Some ((eat t "}") × (IfElse c s s2))
  parseRestOfIfElse c s tkns = Some (tkns × (If c s))

  parseRestOfWrite e [t] = None
  parseRestOfWrite e tkns with parseExp tkns
  ... | None = None
  ... | Some (t × e2) = Some ((eat t ";") × (Writeheap e e2))

  -- Top level parser function; calls the other parsers and converts from the option (token stmt) type to the appropriate stmt
  parseTokens : Tokens → Stmt
  parseTokens tkns with parseStmt1 tkns
  ... | None  = No-op --The program failed to parse
  ... | (Some ([t] × s)) = s
  ... | (Some (t × s)) = No-op --Parser thinks it worked, but didn't finish parsing

  -- Main function; parses and then runs the program
  run : Tokens → RAM
  run t = exec (parseTokens t)



--- Extra Notes ---
-- No ++ is allowed, since right now that reads as a plus operator (solution would be to make it process to "++":t:tkns)
-- Tokenizer should split on ; , { } ( ) operators etc
