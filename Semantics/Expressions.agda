module Semantics.Expressions where

  open import Language.miCro
  open import Language.miCro_parser
  open import Agda.Builtin.Bool

  ---String Functions, included here since so far only expressions use these
  ---These functions help with alphabetical ordering of expressions that include variables
  CharListCompare : List Char → List Char → Order
  CharListCompare [] [] = Equal
  CharListCompare [] (c ∷ chars) = Less
  CharListCompare (c ∷ chars) [] = Greater
  CharListCompare (c1 ∷ chars1) (c2 ∷ chars2) with compare (primCharToNat c1) (primCharToNat c2)
  ... | Less = Less
  ... | Greater = Greater
  ... | Equal = CharListCompare chars1 chars2

  StringAlphaCompare : String → String → Order
  StringAlphaCompare str1 str2 = CharListCompare (primStringToList str1) (primStringToList str2)



  --- Canonical Forms for Expressions ---
  -- Canonicalization works by first "linearizing" (changing to one minus joining two chains of plus, so minimal "tree-like" structures are involved)
  -- Next all like terms on each side of the minus are combined, and after that the two sides are compared and terms are canceled as appropriate
  -- Each side of the minus is the alphabetized by the name of the variable being used, or pushed to the very end in the case of constants
  -- CFE as used below stands for "canonical form expression"

  --Helper that returns back two chains of plus, the second of which is to be joined by a minus to the first
  --Also "filters down" the times
  {-# TERMINATING #-} --agda being pretty strange about terminating this
  CFELinearize : (Pair Exp Exp) → Exp → (Pair Exp Exp)
  CFELinearize (e1 × e2) (const n) = ((plus (const n) e1) × e2)
  CFELinearize (e1 × e2) (readVar str) = CFELinearize (e1 × e2) (times (readVar str) 1) --This should never be the case for handling Hoare Triples, but useful if we need canonical forms otherwise
  CFELinearize (e1 × e2) (times (const n) m) = ((plus (const (n * m)) e1) × e2)
  CFELinearize (e1 × e2) (times (readVar str) n) = ((plus (times (readVar str) n) e1) × e2)
  CFELinearize (e1 × e2) (times (plus e3 e4) n) = CFELinearize (e1 × e2) (plus (times e3 n) (times e4 n))
  CFELinearize (e1 × e2) (times (minus e3 e4) n) = CFELinearize (e1 × e2) (minus (times e3 n) (times e4 n))
  CFELinearize (e1 × e2) (times (times e3 m) n) = CFELinearize (e1 × e2) (times e3 (m * n))
  CFELinearize (e1 × e2) (plus e3 e4) = CFELinearize (CFELinearize (e1 × e2) e4) e3
  CFELinearize (e1 × e2) (minus e3 e4) = let (e1' × e2') = CFELinearize (e2 × e1) e4 in CFELinearize (e2' × e1') e3 --flip then flip back to get the stuff from e4 (being subtracted) on the opposite side
  --CFELinearize (e1 × e2) e3 = (e1 × e2) --shouldn't reach this point

  --Another helper that turns the exp from a tree into a more linear structure;
  --Makes sure that all plus/minus is between a const/times of Var first, and then more plus/minus like a list
  --Removes all instances of (plus (plus e1 e2) e3) etc
  CFELinMain : Exp → Exp
  CFELinMain e  = let (e1' × e2') = CFELinearize (const zero × const zero) e in (minus e1' e2')

  --Pair of functions to combine all the like terms on each side of the minus
  --This function assumes only plus is used on "atomic" expressions (times of read, or const)
  --Searches e2 for all cases of e1, removes and absorbs them into e1
  CFECombineTerms : Exp → Exp → (Pair Exp Exp)
  CFECombineTerms e1 (const 0) = (e1 × (const 0))
  CFECombineTerms (times (readVar str1) n) (plus (times (readVar str2) m) exp) with primStringEquality str1 str2
  ... | true = CFECombineTerms (times (readVar str1) (n + m)) exp
  ... | false = let (e1' × e2') = (CFECombineTerms (times (readVar str1) n) exp) in (e1' × (plus (times (readVar str2) m) (e2')))
  CFECombineTerms (times (readVar str1) n) (times (readVar str2) m) with primStringEquality str1 str2
  ... | true = ((times (readVar str1) (n + m)) × (const zero))
  ... | false = ((times (readVar str1) n) × (times (readVar str2) m))
  CFECombineTerms (const n) (plus (const m) exp) = CFECombineTerms (const (n + m)) exp
  CFECombineTerms (const n) (const m) = (const (n + m) × const zero)
  CFECombineTerms e1 (plus e2 e3) = let (e1' × e2') = (CFECombineTerms e1 e3) in (e1' × (plus e2 e2'))
  CFECombineTerms e1 e2 = (e1 × e2) --should never reach here, but just need to catch all cases and errors

  --Currently only functional when used at this appropriate point in the canonicalization process; will not work on an expression of any form
  CFECombineMain : Exp → Exp
  CFECombineMain (plus e1 e2) with CFECombineTerms e1 e2
  ... | (e1' × const zero) = e1'
  ... | (e1' × (times (readVar str) n)) = plus e1' (times (readVar str) n)
  ... | (e1' × (plus e2' e3')) = plus e1' (CFECombineMain (plus e2' e3'))
  ... | (e1' × e2') = plus e1' e2' --Don't think we should ever reach this based on the return types of CFECombineTerms
  CFECombineMain e = const 0 --again this should never be reached


  CFECancelHelper : Exp → Exp → (Pair Exp Exp)
  CFECancelHelper (times (readVar str1) n) (plus (times (readVar str2) m) e2) with primStringEquality str1 str2
  ... | true = boolIfElse (NatLess n m) ((const zero) × (plus (times (readVar str1) (m - n)) e2)) ((times (readVar str1) (n - m)) × (e2))
  ... | false = let (e1' × e2') = (CFECancelHelper (times (readVar str1) n) e2) in (e1' × (plus (times (readVar str2) m) e2'))
  CFECancelHelper (times (readVar str1) n) (times (readVar str2) m) with primStringEquality str1 str2
  ... | true = boolIfElse (NatLess n m) ((const zero) × (times (readVar str1) (m - n))) ((times (readVar str1) (n - m)) × (const zero))
  ... | false = ((times (readVar str1) n) × (times (readVar str2) m))
  CFECancelHelper (const n) (plus (const m) e2) with compare n m
  ... | Less = ((const zero) × (plus (const (m - n)) e2))
  ... | Greater = ((const (n - m)) × e2)
  ... | Equal = ((const zero) × e2)
  CFECancelHelper (const n) (const m) with compare n m
  ... | Less = ((const zero) × (const (m - n)))
  ... | Greater = ((const (n - m)) × (const zero))
  ... | Equal = ((const zero) × (const zero))
  CFECancelHelper e1 (plus e2 e3) = let (e1' × e2') = (CFECancelHelper e1 e3) in (e1' × (plus e2 e2'))
  CFECancelHelper e1 e2 = (e1 × e2)

  --Addition helper, that "pushes addition through minus"
  CPlus : Exp → Exp → Exp
  CPlus e1 (minus e2 e3) = (minus (plus e1 e2) e3)
  CPlus e1 e2 = (plus e1 e2)

  --Iterates through a minus structure, cancelling any like terms and sending them to the appropriate side
  CFECancelMain : Exp → Exp
  CFECancelMain (minus (plus e1 e2) e3) with CFECancelHelper e1 e3
  ... | ((const zero) × e2') = CFECancelMain (minus e2 e2')
  ... | (e1' × (const zero)) = (plus e1' e2)
  ... | (e1' × e2') = CPlus e1' (CFECancelMain (minus e2 e2')) --Using a helper function here to add e1' below the minus after the rest of the work is done
  CFECancelMain e = e --Shouldn't ever get a non-minus structure to work with at present

  ExpAlphaCompare : Exp → Exp → Order
  ExpAlphaCompare (times (readVar str1) n) (times (readVar str2) m) = StringAlphaCompare str1 str2
  ExpAlphaCompare (times (readVar str) n) e2 = Less
  ExpAlphaCompare (const n) (times (readVar str) m) = Greater
  ExpAlphaCompare (const n) e2 = Less
  ExpAlphaCompare e1 e2 = Equal

  --Takes a "least so far" expression and plus-list of exps, returns the least element and the rest of the plus-list
  CFEAlphaHelper : Exp → Exp → (Pair Exp Exp)
  CFEAlphaHelper e1 (plus e2 e3) with ExpAlphaCompare e1 e2
  ... | Greater = let (e1' × e2') = (CFEAlphaHelper e2 e3) in (e1' × (plus e1 e2'))
  ... | other = let (e1' × e2') = (CFEAlphaHelper e1 e3) in (e1' × (plus e2 e2'))
  CFEAlphaHelper e1 e2 with ExpAlphaCompare e1 e2
  ... | Greater = (e2 × e1)
  ... | other = (e1 × e2)

  CFEAlphabetize : Exp → Exp
  CFEAlphabetize (minus e1 e2) = (minus (CFEAlphabetize e1) (CFEAlphabetize e2))
  CFEAlphabetize (plus e1 e2) = let (e1' × e2') = (CFEAlphaHelper e1 e2) in (plus e1' (CFEAlphabetize e2'))
  CFEAlphabetize other = other


  --Top-level function just stacks the appropriate functions; first linearize, then combine like terms, then cancel like terms (and then alphabetize later)
  CFExp : Exp → Exp
  CFExp e with CFELinMain e
  ... | (minus e1 e2) = CFEAlphabetize (CFECancelMain (minus (CFECombineMain e1) (CFECombineMain e2)))
  ... | exp = (const zero) --CFELinMain can't return anything other than a minus structure (at least currently)

  --- Extra expression functions, not part of the canonicalization process, but rely on their arguments being in that form to function
  -- Might later change these to a CFE Equality and a general equality that first applies the C Form itself?

  --This will test if a two given expressions are always equal;
  --Assumes proper canonical form is used, so the two expressions should be identical in structure and content
  ExpEquality : Exp → Exp → Bool
  ExpEquality (minus e1 e2) (minus e3 e4) = boolAnd (ExpEquality e1 e3) (ExpEquality e2 e4)
  ExpEquality (plus e1 e2) (plus e3 e4) = boolAnd (ExpEquality e1 e3) (ExpEquality e2 e4)
  ExpEquality (times e1 n) (times e2 m) = boolAnd (ExpEquality e1 e2) (NatEquality n m)
  ExpEquality (readVar str1) (readVar str2) = primStringEquality str1 str2
  ExpEquality (const n) (const m) = NatEquality n m
  ExpEquality e1 e2 = false --Any other structure indicates an error in canonical form

  --Less than gets messy due to cases
  {-# TERMINATING #-} --Terminates due to the structure of the exps after canonicalization; may not terminate on all inputs
  ExpLessThan : Exp → Exp → Bool
  ExpLessThan (minus e1 e2) (plus e3 e4) = ExpLessThan e1 (plus e3 e4)
  ExpLessThan (minus e1 e2) (times e3 m) = ExpLessThan e1 (times e3 m)
  ExpLessThan (minus e1 e2) (const m) = ExpLessThan e1 (const m)
  ExpLessThan (minus e1 e2) (minus e3 e4) = boolOr (boolOr (boolAnd (ExpLessThan e1 e3) (ExpLessThan e4 e2)) (boolAnd (ExpLessThan e1 e3) (ExpEquality e4 e2))) (boolAnd (ExpEquality e1 e3) (ExpLessThan e4 e2))
  ExpLessThan (plus e1 e2) (plus e3 e4) = boolOr (boolOr (boolAnd (ExpLessThan e1 e3) (ExpLessThan e2 e4)) (boolAnd (ExpLessThan e1 e3) (ExpEquality e2 e4))) (boolAnd (ExpEquality e1 e3) (ExpLessThan e2 e4))
  ExpLessThan (times e1 n) (times e2 m) = (boolAnd (ExpEquality e1 e2) (NatLess n m))
  ExpLessThan (times e1 n) (plus e3 e4) = boolOr (boolOr (ExpLessThan (times e1 n) e3) (ExpLessThan (times e1 n) e4)) (boolAnd (ExpEquality (times e1 n) e3) (ExpLessThan (const zero) (e4)))
  ExpLessThan (const n) (plus e1 e2) = ExpLessThan (const n) e2 --e1 won't be a const so we can skip that comparison
  ExpLessThan (const n) (const m) = NatLess n m
  ExpLessThan e1 e2 = false

  --"Canonical" times, which applies times to an exp "at the lowest level" so that the given multiple is applied directly to each variable and absorbed by each const
  -- This appears at the bottom since it is not used by the canonicalization process, but in other parts of the Hoare Triple Logic where this function can be used to maintian C Form
  -- In place of a regular times followed a complete re-canonicalization
  CTimes : Exp → Nat → Exp
  CTimes (plus e1 e2) n = (plus (CTimes e1 n) (CTimes e2 n))
  CTimes (minus e1 e2) n = (minus (CTimes e1 n) (CTimes e2 n))
  CTimes (times e1 m) n = (times (CTimes e1 n) m)
  CTimes (const m) n = (const (m * n))
  CTimes exp n = (times exp n)

  -- Replaces all instances of n*Var in e2 with e1
  -- Canonical forms are not necessary for this, but will only work with var*n directly, not times (plus var something) n, etc.
  -- So At minimum CTimes should be applied
  ReplaceInExp : Nat → String → Exp → Exp → Exp
  ReplaceInExp n1 var e1 (times (readVar str) n2) with primStringEquality var str
  ... | false = (times (readVar str) n2)
  ... | true = boolIfElse (NatEquality n1 n2) (e1) (times (readVar str) n2)
  ReplaceInExp n var e1 (plus e2 e3) = plus (ReplaceInExp n var e1 e2) (ReplaceInExp n var e1 e3)
  ReplaceInExp n var e1 (minus e2 e3) = minus (ReplaceInExp n var e1 e2) (ReplaceInExp n var e1 e3)
  ReplaceInExp n var e1 (times e2 n2) = times (ReplaceInExp n var e1 e2) n2
  ReplaceInExp n var e1 e2 = e2 --All that remains are illegal heap ops, deprecated readVar++, and const

  --Renames all instances of str in the exp with str with nat appended
  RenameInExp : Nat → Exp → String → Exp
  RenameInExp n1 (readVar str) var with primStringEquality str var
  ... | false = (readVar str)
  ... | true = (readVar (primStringAppend str (primShowNat n1)))
  RenameInExp n (plus e1 e2) var = plus (RenameInExp n e1 var) (RenameInExp n e2 var)
  RenameInExp n (minus e1 e2) var = minus (RenameInExp n e1 var) (RenameInExp n e2 var)
  RenameInExp n (times e1 n2) var = times (RenameInExp n e1 var) n2
  RenameInExp n e1 var = e1 --All that remains are illegal heap ops, deprecated readVar++, and const

  --Checks to see if the given expression contains the given variable,
  --so we know when we have to replace or modify conditions
  ExpContainsVar : String → Exp → Bool
  ExpContainsVar var (readVar str) = primStringEquality var str
  ExpContainsVar var (plus e1 e2) = boolOr (ExpContainsVar var e1) (ExpContainsVar var e2)
  ExpContainsVar var (minus e1 e2) = boolOr (ExpContainsVar var e1) (ExpContainsVar var e2)
  ExpContainsVar var (times e n) = ExpContainsVar var e
  ExpContainsVar var e = false --We don't allow heap operations, so excluding those nothing else could contain the variable

  --Flag data type to help the Comparison function below pass back information
  data Orientation {a} (A : Set a) : Set a where
    Same : A → Orientation A
    Flipped : A → Orientation A

  ToggleOrientation : ∀ {A : Set} →  Orientation A → Orientation A
  ToggleOrientation (Same x) = Flipped x
  ToggleOrientation (Flipped x) = Same x
  

  --Takes two expressions which appear on either side of a comparison and returns them as a pair
  --Where the first exp is now a single var or const zero
  --The chosen var is the first one to appear in the left expression
  --Sometimes the comparison must be flipped for the Canonical form to be reached, so the Orientation type does this (eg 3 < x needs to be in the form x > 3)
  {-# TERMINATING #-} --This should terminate, but I think agda doesn't recognize that CFExp only returns certain forms
  CFCompHelper : Exp → Exp → Orientation (Pair Exp Exp)
  CFCompHelper (const n) (const m) = Same (const n × const m)
  CFCompHelper (const n) (plus e1 e2) = Flipped (e1 × (CFExp (minus (const n) e2))) --Exps are in CForm, so e1 must be a readVar  
  CFCompHelper (const n) (minus e1 (plus e2 e3)) = Same (e2 × (CFExp (minus e1 (plus (const n) e3))))
  CFCompHelper (const n) (minus e1 (times (readVar var) m)) = Same ((times (readVar var) m) × (CFExp (minus e1 (const n))))
  CFCompHelper (const n) (minus e1 e2) = ToggleOrientation (CFCompHelper (minus e1 e2) (const n))
  CFCompHelper (const n) (times (readVar var) m) = Flipped ((times (readVar var) m) × (const n))
  CFCompHelper (times (readVar var) n) e = Same ((times (readVar var) n) × e)
  CFCompHelper (plus (times (readVar var) n) e2) e3 = Same ((times (readVar var) n) × (CFExp (minus e3 e2)))
  CFCompHelper (minus (times (readVar var) n) e2) e3 = Same ((times (readVar var) n) × (CFExp (plus e3 e2)))
  CFCompHelper (minus (plus (times (readVar var) n) e2) e3) e4 = Same ((times (readVar var) n) × (CFExp (minus (plus e4 e3) e2)))
  CFCompHelper (minus (const n) (plus e2 e3)) e4 = ToggleOrientation (CFCompHelper (CFExp (plus e4 (plus e2 e3))) (const n)) --CFExp on these plus terms will give back more plus between atomics, so it should terminate despite what agda claims
  CFCompHelper e1 e2 = Same (e1 × e2) --Shouldn't be reaching here since we're dealing with only canonical forms

  --Main function just cancels out similar terms from each side before passing to the helper term
  CFComparison : Exp → Exp → Orientation (Pair Exp Exp)
  CFComparison e1 e2 with CFExp (minus e1 e2)
  ... | (minus e1' e2') = CFCompHelper e1' e2'
  ... | e = CFCompHelper e (const zero)
  
  
