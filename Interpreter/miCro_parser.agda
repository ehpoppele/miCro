-- First: Read from file into string --

-- process env = initial environment read from string
-- process prog = instructions read from string
-- run exec env prog, and return (print?) output

-- Tokens and related functions --
-- At this point we assume the input file has been parsed into tokens type
-- Token type is a list of strings with all whitespace removed, separated on special characters
-- So "while" should be one list entry, with the proceeding "(" being it's own, and so on.

module Interpreter.miCro_parser where

  open import Interpreter.miCro

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
  -- OptionE here used for Option Error, so that a string explaining the error may be attached to the None type
  data OptionE {a} (A : Set a) : Set a where
    None : String → OptionE A
    Some : A → OptionE A

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
  eat [t] str = [t]
  eat (s1 :t: tkns) s2 with primStringEquality s1 s2
  ... | false = [t]
  ... | true = tkns

  -- Returns the first token as a name (could add checking to confirm it isn't a number/doesn't use a unallowed symbol)
  eatName : Tokens → String
  eatName [t] = ""
  eatName (s :t: tkns) = s

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

  -- Checks to see if a word is a keyword or if it should be treated as a var (assumes numbers filtered already; may change that later)
  -- Maybe should get a better workaround than this; current issue is parseExp will read so much as a var, esp. an issue with its call in parseComp
  isVarName : String → Bool
  isVarName "" = false
  isVarName "true" = false
  isVarName "false" = false
  isVarName "while" = false
  isVarName "and" = false
  isVarName "or" = false
  isVarName "(" = false
  isVarName ")" = false
  isVarName "[" = false
  isVarName "]" = false
  isVarName str = true
  -- may need more cases to handle symbols; will figure that out

  -- Parsing functions, directly interacting with the stream and parsing it. Split into condition, expression, and statement

  -- Parse functions for Conditions and Expressions, which are handled separately --
  {-# TERMINATING #-}
  parseExp : Tokens → (OptionE (Pair Tokens Exp))
  parseSum : Tokens → (OptionE (Pair Tokens Exp))
  parseMult : Tokens → (OptionE (Pair Tokens Exp))
  parseRestOfSum : Exp → Tokens → (OptionE (Pair Tokens Exp))
  parseRestOfMult : Exp → Tokens → (OptionE (Pair Tokens Exp))
  parseAtom : Tokens → (OptionE (Pair Tokens Exp))
  parseVar : Tokens → (OptionE (Pair Tokens Exp))
  parseConst : Tokens → (OptionE (Pair Tokens Exp))

  parseExp [t] = None "Expected an expression but tokens ended; possibly attempted to eat a token that wasn't there"-- need to make sure this works
  parseExp tkns = parseSum tkns

  parseSum tkns with parseMult tkns
  ... | None s = None s
  ... | Some (tkns' × e) = parseRestOfSum e tkns'

  parseRestOfSum e ("+" :t: tkns) with parseMult tkns
  ... | None s = None s
  ... | Some (tkns' × e2) = parseRestOfSum (plus e e2) tkns'
  parseRestOfSum e ("-" :t: tkns) with parseMult tkns
  ... | None s = None s
  ... | Some (tkns' × e2) = parseRestOfSum (minus e e2) tkns'
  parseRestOfSum e tkns = Some (tkns × e)

  parseMult tkns with parseAtom tkns
  ... | None s = None s
  ... | Some (tkns' × e) = parseRestOfMult e tkns'

  parseRestOfMult e ("*" :t: tkns) with parseConst tkns
  ... | None s = None s
  ... | Some (tkns' × e2) = Some (tkns' × (times e e2))
  parseRestOfMult e tkns = Some (tkns × e)

  parseAtom ("[" :t: tkns) with parseExp tkns
  ... | None s = None s
  ... | Some (tkns' × e) = Some ((eat tkns' "]") × e)
  parseAtom (str :t: tkns) with isNumber (primStringToList str)
  ... | true = Some (tkns × (const (stringToNat str)))
  ... | false = parseVar (str :t: tkns)
  parseAtom [t] = None "Tokens ended unexpectedly while parsing an expression" --I think, might change later

  parseVar (str :t: tkns) with isVarName str
  ... | false = None "Reserved word or symbol used in an expression"
  ... | true = Some (tkns × (readVar str))
  parseVar [t] = None "Empty tokens while parsing a var inside an expression; it shouldn't be possible to reach this line."

  -- Needed since parsing a mult has to then parse a num without possibility of parens or vars
  parseConst (str :t: tkns) with isNumber (primStringToList str)
  ... | true = Some (tkns × (const (stringToNat str)))
  ... | false = None "Attempted multiplication by something other than a const valued number"
  parseConst [t] = None "Attempted to multiply with empty tokens"

  {-# TERMINATING #-} --Note: Will need to add ability to process literal booleans (t/f) later, unless not needed
  parseCnd : Tokens → OptionE (Pair Tokens Cnd)
  parseDisj : Tokens → OptionE (Pair Tokens Cnd)
  parseConj : Tokens → OptionE (Pair Tokens Cnd)
  parseNeg : Tokens → OptionE (Pair Tokens Cnd)
  parseComp : Tokens → OptionE (Pair Tokens Cnd)
  parseBaseCnd : Tokens → OptionE (Pair Tokens Cnd)
  parseRestOfDisj : Cnd → Tokens → OptionE (Pair Tokens Cnd)
  parseRestOfConj : Cnd → Tokens → OptionE (Pair Tokens Cnd)
  parseRestOfComp : Exp → Tokens → OptionE (Pair Tokens Cnd)

  parseCnd [t] = None "Expected a condition but tokens ended; could have attempted to eat a token that wasn't there"
  parseCnd tkns = parseDisj tkns

  parseDisj tkns with parseConj tkns
  ... | None s = None s
  ... | Some (tkns' × c) = parseRestOfDisj c tkns'

  parseRestOfDisj c ("or" :t: tkns) with parseConj tkns
  ... | None s = None s
  ... | Some (tkns' × c2) = parseRestOfDisj (c Or c2) tkns'
  parseRestOfDisj c tkns = Some (tkns × c)

  parseConj tkns with parseNeg tkns
  ... | None s = None s
  ... | Some (tkns' × c) = parseRestOfConj c tkns'

  parseRestOfConj c ("and" :t: tkns) with parseNeg tkns
  ... | None s = None s
  ... | Some (tkns' × c2) = parseRestOfConj (c And c2) tkns'
  parseRestOfConj c tkns = Some (tkns × c)

  parseNeg ("not" :t: tkns) with parseNeg tkns
  ... | None s = None s
  ... | Some (tkns' × c) = Some (tkns' × (Not c))
  parseNeg tkns = parseBaseCnd tkns

  parseBaseCnd ("(" :t: tkns) with parseCnd tkns
  ... | None s = None s
  ... | Some (tkns' × c) = Some ((eat tkns' ")") × c)
  parseBaseCnd ("true" :t: tkns) = Some (tkns × (cndBool true))
  parseBaseCnd ("false" :t: tkns) = Some (tkns × (cndBool false))
  parseBaseCnd tkns = parseComp tkns

  parseComp tkns with parseExp tkns
  ... | None s = None "Attempted to parse a condition but found no appropriate symbols" --Since we've tried to parse everything else, we can safely assume this is either an expression or a syntax error
  ... | Some (tkns' × e) = parseRestOfComp e tkns'

  parseRestOfComp e ("==" :t: tkns) with parseExp tkns
  ... | None s = None s
  ... | Some (tkns' × e2) = Some (tkns' × (e == e2))
  parseRestOfComp e ("!=" :t: tkns) with parseExp tkns
  ... | None s = None s
  ... | Some (tkns' × e2) = Some (tkns' × (e != e2))
  parseRestOfComp e ("<=" :t: tkns) with parseExp tkns
  ... | None s = None s
  ... | Some (tkns' × e2) = Some (tkns' × (e <= e2))
  parseRestOfComp e (">=" :t: tkns) with parseExp tkns
  ... | None s = None s
  ... | Some (tkns' × e2) = Some (tkns' × (e >= e2))
  parseRestOfComp e ("<" :t: tkns) with parseExp tkns
  ... | None s = None s
  ... | Some (tkns' × e2) = Some (tkns' × (e < e2))
  parseRestOfComp e (">" :t: tkns) with parseExp tkns
  ... | None s = None s
  ... | Some (tkns' × e2) = Some (tkns' × (e > e2))
  parseRestOfComp e tkns = None "Found an expression but no comparison while attempting to parse a condition"

  -- Statement parse functions --
  {-# TERMINATING #-}
  parseStmt1 : Tokens → (OptionE (Pair Tokens Stmt))
  parseStmt2 : (OptionE (Pair Tokens Stmt)) → (OptionE (Pair Tokens Stmt))
  parseStmt3 : (OptionE (Pair Tokens Stmt)) → (OptionE (Pair Tokens Stmt))
  parseSingleStmt : Tokens → (OptionE (Pair Tokens Stmt))
  parseRestOfWhile : Cnd → Tokens → (OptionE (Pair Tokens Stmt))
  parseRestOfIf : Cnd → Tokens → (OptionE (Pair Tokens Stmt))
  parseRestOfIfElse : Cnd → Stmt → Tokens → (OptionE (Pair Tokens Stmt))
  parseRestOfWrite : Exp → Tokens → (OptionE (Pair Tokens Stmt))

  -- Main Stmt parser; this continually creates a sequence of parsed stmts 
  parseStmt1 [t] = None "Attempted to parse a statement that ended unexpectedly"
  parseStmt1 tkns = parseStmt2 (parseSingleStmt tkns)

  -- Helper function for Stmt1; if these combined I would have to write out parseSingleStmt tkns about five times (since I can't use "with" in a "let ... in"), which would mean five times slower parsing
  parseStmt2 (None str) = None str
  parseStmt2 (Some (tkns × s)) with stopper tkns
  ... | true = (Some ([t] × s))
  ... | false = parseStmt3 (Some (tkns × s)) -- Now we want "(Some ([t] × (Seq s (parseStmt1 t))))", but we must first check that parseStmt1 gives a Some return

  -- Another helper, since we need to make a Seq in second case above, but need to know we got back some Stmt and not a None option
  parseStmt3 (None str) = None str
  parseStmt3 (Some (tkns × s)) with parseStmt1 tkns
  ... | None str = None str
  ... | Some (tkns' × s2) = (Some ([t] × (Seq s s2))) --Not sure what tkns' is doing here- should this be changed to [t] with non-empty tokens raising an error?

  -- Parses a single statement from the tokens; does the "heavy lifting" stmt parsing
  parseSingleStmt [t] = (Some ([t] × No-op)) -- don't know if I need this, but just want to catch errors
  parseSingleStmt ("while" :t: tkns) with (parseCnd (eat tkns "("))
  ... | None str = None str
  ... | Some (tkns' × c) = parseRestOfWhile c (eat (eat tkns' ")") "{")
  parseSingleStmt ("if" :t: tkns) with (parseCnd (eat tkns "("))
  ... | None str = None str
  ... | Some (tkns' × c) = parseRestOfIf c (eat (eat tkns' ")") "{")
  parseSingleStmt ("new " :t: tkns) with parseExp (eat (eat tkns (eatName tkns)) "=") -- A little cheaty since this sort of looks two tokens ahead
  ... | None str = None str
  ... | Some (tkns' × e) = Some ((eat tkns' ";") × (AssignPtr (eatName tkns) e))
  parseSingleStmt ("*" :t: tkns) with parseExp tkns
  ... | None str = None str
  ... | Some (tkns' × e) = parseRestOfWrite e (eat tkns' "=")
  parseSingleStmt (name :t: "=" :t: "*" :t: tkns) with parseExp tkns --This really breaks the idea of looking only one ahead; could also be written to be part of a RestOfVar under the next line
  ... | None str = None str 
  ... | Some (tkns' × e) = Some ((eat tkns' ";") × (AssignVar (name) (readAddress e)))
  parseSingleStmt tkns with parseExp (eat (eat tkns (eatName tkns)) "=") --This will catch any other errors, as eat will return [t] if it can't eat the expeted token, leading to parseExp returning None
  ... | None str = None str
  ... | Some (tkns' × e) = Some ((eat tkns' ";") × (AssignVar (eatName tkns) e))

  -- Parses the rest of a multi-part statement
  
  parseRestOfWhile c tkns with parseStmt1 tkns
  ... | None str = None str
  ... | Some (tkns' × s) = Some ((eat tkns' "}") × (While c s))

  parseRestOfIf c tkns with parseStmt1 tkns
  ... | None str = None str
  ... | Some (tkns' × s) = parseRestOfIfElse c s (eat tkns' "}")

  parseRestOfIfElse c s ("else" :t: tkns) with parseStmt1 (eat tkns "{")
  ... | None str = None str
  ... | Some (tkns' × s2) = Some ((eat tkns' "}") × (IfElse c s s2))
  parseRestOfIfElse c s tkns = Some (tkns × (If c s))

  parseRestOfWrite e tkns with parseExp tkns
  ... | None str = None str
  ... | Some (tkns' × e2) = Some ((eat tkns' ";") × (WriteHeap e e2))

  -- Top level parser function; calls the other parsers and converts from the option (token stmt) type to the appropriate stmt
  parseTokens : Tokens → Stmt
  parseTokens tkns with parseStmt1 tkns
  ... | None str  = (AssignVar str (const 0)) --The program failed to parse; this is the best way of passing back the string...
  ... | (Some ([t] × s)) = s
  ... | (Some (tkns' × s)) = (Seq (AssignVar "Parsing finished, but didn't read all tokens" (const 0)) s) -- Not sure if this can even happen, honestly

  -- Main function; parses and then runs the program with empty intial RAM
  run : Tokens → RAM
  run tkns = exec ([e] & [h]) (parseTokens tkns)
