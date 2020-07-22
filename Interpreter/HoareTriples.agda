module Interpreter.HoareTriples where

  open import Interpreter.miCro
  open import Interpreter.miCro_parser
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open import Agda.Builtin.Bool

  data evalsTo : RAM → Exp → Nat → Set where
    evalsProof : ∀ {m : RAM} {x : Exp} {n : Nat}
      → (eval m x) ≡ n
      ------------
      → evalsTo m x n

  basicEval : evalsTo ([e] & [h]) (readVar "x") zero
  basicEval = evalsProof refl

  --Change checks to to checks true?
  data checksTo : RAM → Cnd → Bool → Set where
    checksProof : ∀ {m : RAM} {c : Cnd} {b : Bool}
      → (check m c) ≡ b
      -------------------
      → checksTo m c b

  basicCheck : checksTo ([e] & [h]) ((readVar "x") <= (const 1)) true
  basicCheck = checksProof refl

  data execsTo : RAM → Stmt → RAM → Set where
    execsProof : ∀ {m1 m2 : RAM} {s : Stmt}
      → (exec m1 s) ≡ m2
      ----------------------------
      → execsTo m1 s m2

  basicExec : execsTo ([e] & [h]) (If ((readVar "X") == (const 0)) (AssignVar "X" (plus (readVar "X") (const 1)))) (((Var "X" 1) :e: [e])& [h])
  basicExec = execsProof refl

------------------------------------

  data VarRestriction : Set where
    VarRstr : Nat → String → String → Exp → VarRestriction --Could clean this up; for now it's Multiplier → varName → ComparisonString → thing compared to. Maybe make comparisons a distinct thing/subset of Cnd?

  data StateSet : Set where
    NoState : StateSet --used when no state satisfies the conditions
    --state set with all vars to zero?
    [s] : StateSet
    _:S:_ : VarRestriction → StateSet → StateSet

  StateJoin : StateSet → StateSet → StateSet
  StateJoin NoState s = NoState
  StateJoin s NoState = NoState
  StateJoin [s] s = s
  StateJoin s [s] = s
  StateJoin (v1 :S: s1) (v2 :S: s2) = StateJoin s1 (v1 :S: (v2 :S: s2)) 

  data StateDisj : Set where
    Only : StateSet → StateDisj
    _StOr_ : StateSet → StateDisj → StateDisj


---String Functions
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

---Expression functions; used to test for comparisons between expressions

  --Condensed form functions, maybe will call this canonical later but it has no alphabetization for vars
  --But for now just condenses an exp into one const and one term for each variable used
  --const always at the end, but vars go in any order
  --Order of functions is : linearize expressions, with split for minus
  --Combine all like terms, pushing consts to end (still on appropriate side of minus division)
  --Aplhabetization would then follow 

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
  CFELinearize (e1 × e2) e3 = (e1 × e2) --shouldn't reach this point

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
  ... | (e1' × (plus e2' e3')) = plus e1 (CFECombineMain (plus e2' e3'))
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
  ExpLessThan : Exp → Exp → Bool
  ExpLessThan (minus e1 e2) (plus e3 e4) = ExpLessThan e1 (plus e3 e4)
  ExpLessThan (minus e1 e2) (minus e3 e4) = boolOr (boolOr (boolAnd (ExpLessThan e1 e3) (ExpLessThan e4 e2)) (boolAnd (ExpLessThan e1 e3) (ExpEquality e4 e2))) (boolAnd (ExpEquality e1 e3) (ExpLessThan e4 e2))
  ExpLessThan (plus e1 e2) (plus e3 e4) = boolOr (boolOr (boolAnd (ExpLessThan e1 e3) (ExpLessThan e2 e4)) (boolAnd (ExpLessThan e1 e3) (ExpEquality e2 e4))) (boolAnd (ExpEquality e1 e3) (ExpLessThan e2 e4))
  ExpLessThan (times e1 n) (times e2 m) = boolOr (boolOr (boolAnd (ExpLessThan e1 e2) (NatLess n m)) (boolAnd (ExpLessThan e1 e2) (NatEquality n m))) (boolAnd (ExpEquality e1 e2) (NatLess n m))
  ExpLessThan (const n) (const m) = NatLess n m
  ExpLessThan e1 e2 = false

 --"Canonical" times, which applies times to an exp "at the lowest level" so that the given multiple is applied directly to each variable and absorbed by each const 
  CTimes : Exp → Nat → Exp
  CTimes (plus e1 e2) n = (plus (CTimes e1 n) (CTimes e2 n))
  CTimes (minus e1 e2) n = (minus (CTimes e1 n) (CTimes e2 n))
  CTimes (times e1 m) n = (times (CTimes e1 n) m)
  CTimes (const m) n = (const (m * n))
  CTimes exp n = (times exp n)


--- Condition Functions! ---
---This all assumes conditions are in a canonical form, without Not and with Or on the outermost level only; also Or should be x Or (y Or ...)
---Canonical Form also assumes all comparisons have one side with a single variable (and mult by const; by 1 at minimum); not sure how this would work out...
---Also need the forms to have EVERY variable multiplied by a const (so add times 1 where needed) as this makes later work easier

{- will take a Cnd to which a NOT was attached and simplify so the NOT can be removed
  CndFlip : Cnd → Cnd
  CndFlip -}

  --This will need an overhaul now
  AlwaysTrue : Cnd → Bool
  AlwaysTrue (cndBool true) = true
  AlwaysTrue (cndBool false) = false
  AlwaysTrue (c1 Or c2) = boolOr (AlwaysTrue c1) (AlwaysTrue c2)
  AlwaysTrue (c1 And c2) = boolAnd (AlwaysTrue c1) (AlwaysTrue c2)
  AlwaysTrue (Not c) with AlwaysTrue c --Don't have a boolNot function implemented yet; maybe should do that
  ... | true = false
  ... | false = true
  AlwaysTrue (e1 == e2) = ExpEquality (CFExp e1) (CFExp e2)
  AlwaysTrue (e1 != e2) with ExpEquality e1 e2
  ... | true = false
  ... | false = true
  AlwaysTrue (e1 < e2) = ExpLessThan e1 e2
  AlwaysTrue (e1 > e2) = ExpLessThan e2 e1
  AlwaysTrue other = false --Other comparisons currently not allowed, so get outta here

--Finds state sets complying with the given non-Or condition
  FindStates : Cnd → StateSet
  FindStates (cndBool true) = [s]
  FindStates (cndBool false) = NoState
  FindStates (c1 And c2) = StateJoin (FindStates c1) (FindStates c2)
  FindStates ((times (readVar str) k) == e) = (VarRstr k str "==" e) :S: [s]
  FindStates ((times (readVar str) k) < e) = (VarRstr k str "<" e) :S: [s]
  FindStates ((times (readVar str) k) > e) = (VarRstr k str ">" e) :S: [s]
  FindStates ((times (readVar str) k) != e) = (VarRstr k str "!=" e) :S: [s]
  FindStates other = NoState --Currently not allowing any other conditions to keep it simple

--Finds state sets complying with the given condition; handles Or then passes off the rest
  StatesSatisfying : Cnd → StateDisj
  StatesSatisfying (c1 Or c2) = (FindStates c1) StOr (StatesSatisfying c2)
  StatesSatisfying c = Only (FindStates c)

  --Checks to see if the given expression contains the given variable,
  --so we know when we have to replace or modify conditions
  ContainsVar : String → Exp → Bool
  ContainsVar var (readVar str) = primStringEquality var str
  ContainsVar var (plus e1 e2) = boolOr (ContainsVar var e1) (ContainsVar var e2)
  ContainsVar var (minus e1 e2) = boolOr (ContainsVar var e1) (ContainsVar var e2)
  ContainsVar var (times e n) = ContainsVar var e
  ContainsVar var e = false --We don't allow heap operations, so excluding those nothing else could contain the variable

  --Checks to see if the condition contains the given variable
  --NOTE: currently this assumes the condition is a comparison; it will not break down and/or/etc.
  CndContainsVar : String → Cnd → Bool
  CndContainsVar var (e1 == e2) = boolOr (ContainsVar var e1) (ContainsVar var e2)
  CndContainsVar var (e1 <= e2) = boolOr (ContainsVar var e1) (ContainsVar var e2)
  CndContainsVar var (e1 >= e2) = boolOr (ContainsVar var e1) (ContainsVar var e2)
  CndContainsVar var (e1 != e2) = boolOr (ContainsVar var e1) (ContainsVar var e2)
  CndContainsVar var (e1 < e2) = boolOr (ContainsVar var e1) (ContainsVar var e2)
  CndContainsVar var (e1 > e2) = boolOr (ContainsVar var e1) (ContainsVar var e2)
  CndContainsVar var c = false

  data Side : Set where
    Left : Side
    Right : Side
    NoSide : Side

  --Extra containment function, returning Left Right or NoSide, for what part of a comp Cnd contains the var
  --Could modify some things to have this replace CndContainsVar later
  WhichSideContainsVar : String → Cnd → Side
  WhichSideContainsVar var (e1 == e2) = boolIfElse (ContainsVar var e1) (Left) (boolIfElse (ContainsVar var e2) (Right) (NoSide))
  WhichSideContainsVar var (e1 <= e2) = boolIfElse (ContainsVar var e1) (Left) (boolIfElse (ContainsVar var e2) (Right) (NoSide))
  WhichSideContainsVar var (e1 >= e2) = boolIfElse (ContainsVar var e1) (Left) (boolIfElse (ContainsVar var e2) (Right) (NoSide))
  WhichSideContainsVar var (e1 != e2) = boolIfElse (ContainsVar var e1) (Left) (boolIfElse (ContainsVar var e2) (Right) (NoSide))
  WhichSideContainsVar var (e1 < e2) = boolIfElse (ContainsVar var e1) (Left) (boolIfElse (ContainsVar var e2) (Right) (NoSide))
  WhichSideContainsVar var (e1 > e2) = boolIfElse (ContainsVar var e1) (Left) (boolIfElse (ContainsVar var e2) (Right) (NoSide))
  WhichSideContainsVar var c = NoSide --this function only accepts comparisons conditions, so the rest are disregarded

  -- Replaces all instances of n*Var in e2 with e1
  ReplaceInExp : Nat → String → Exp → Exp → Exp
  ReplaceInExp n1 var e1 (times (readVar str) n2) with primStringEquality var str
  ... | false = (times (readVar str) n2)
  ... | true = e1 --Need to fix this later; but for now it's technically safe to assume n1 = n2
  ReplaceInExp n var e1 (plus e2 e3) = plus (ReplaceInExp n var e1 e2) (ReplaceInExp n var e1 e3)
  ReplaceInExp n var e1 (minus e2 e3) = minus (ReplaceInExp n var e1 e2) (ReplaceInExp n var e1 e3)
  ReplaceInExp n var e1 (times e2 n2) = times (ReplaceInExp n var e1 e2) n2
  ReplaceInExp n var e1 e2 = e2 --All that remains are illegal heap ops, deprecated readVar++, and const 

  -- If string is a variable in Cnd, this multiplies the Cnd (assumed to be a comp)
  -- By nat, then replaces all instances of nat*var in Cnd with exp, and returns that Cnd
  --- !!!!! Need to fix this; change so that instead of times its a "canonical times" that pushes the times down to the "lowest level" (closest to the variables/consts)
  ReplaceInCnd : Nat → String → Exp → Cnd → Cnd
  ReplaceInCnd n var e1 (e2 == e3) with boolOr (ContainsVar var e2) (ContainsVar var e3)
  ... | true = (ReplaceInExp n var e1 (times e2 n)) == (ReplaceInExp n var e1 (times e3 n))
  ... | false = (e2 == e3)
  ReplaceInCnd n var e1 (e2 < e3) with boolOr (ContainsVar var e2) (ContainsVar var e3)
  ... | true = (ReplaceInExp n var e1 (times e2 n)) < (ReplaceInExp n var e1 (times e3 n))
  ... | false = (e2 < e3)
  ReplaceInCnd n var e1 (e2 > e3) with boolOr (ContainsVar var e2) (ContainsVar var e3)
  ... | true = (ReplaceInExp n var e1 (times e2 n)) > (ReplaceInExp n var e1 (times e3 n))
  ... | false = (e2 > e3)
  ReplaceInCnd n var e1 (e2 != e3) with boolOr (ContainsVar var e2) (ContainsVar var e3)
  ... | true = (ReplaceInExp n var e1 (times e2 n)) != (ReplaceInExp n var e1 (times e3 n))
  ... | false = (e2 != e3)
  ReplaceInCnd n var e otherCnd = cndBool false --Need to finish this?

  --Returns a modified version of the given condition, where the given restriction is taken into account
  -- Currently these will sometimes lose their canonical form, which may be an issue
  -- I don't think this function itself relies on the form, however, so maybe can be fixed
  -- By just doing canonicalization later; before AlwaysTrue is evaluated?
  ModifyCnd : VarRestriction → Cnd → Cnd
  ModifyCnd vr (cndBool true) = (cndBool true)
  ModifyCnd vr (cndBool false) = (cndBool false)
  ModifyCnd vr (c1 Or c2) = (ModifyCnd vr c1) Or (ModifyCnd vr c2)
  ModifyCnd vr (c1 And c2) = (ModifyCnd vr c1) And (ModifyCnd vr c2)
  ModifyCnd (VarRstr k var "==" e1) c = ReplaceInCnd k var e1 c
  ModifyCnd (VarRstr k var "!=" e1) c with CndContainsVar var c
  ... | true = c And ((times (readVar var) k) != e1)
  ... | false = c
  ModifyCnd (VarRstr k var "<" e1) (e2 == e3) with WhichSideContainsVar var (e2 == e3)
  ... | Left = (e2 == e3) And (ReplaceInCnd k var (minus e1 (const 1)) ((plus e2 (const 1)) > e3))
  ... | Right = (e2 == e3) And (ReplaceInCnd k var (minus e1 (const 1)) (e2 < (plus e3 (const 1)))) --trust me this works
  ... | NoSide = (e2 == e3)
  ModifyCnd (VarRstr k var "<" e1) (e2 < e3) with WhichSideContainsVar var (e2 < e3)
  ... | Left = (e2 < e3) Or (ReplaceInCnd k var (minus e1 (const 1)) (e2 < e3)) --No plus one like before since we're dealing with a strict less than
  ... | Right = (e2 < e3) And (ReplaceInCnd k var (minus e1 (const 1)) (e2 < e3))
  ... | NoSide = (e2 < e3)
  ModifyCnd (VarRstr k var "<" e1) (e2 > e3) with WhichSideContainsVar var (e2 > e3)
  ... | Left = (e2 > e3) And (ReplaceInCnd k var (minus e1 (const 1)) (e2 > e3))
  ... | Right = (e2 > e3) Or (ReplaceInCnd k var (minus e1 (const 1)) (e2 > e3))
  ... | NoSide = (e2 > e3)
  ModifyCnd (VarRstr k var ">" e1) (e2 == e3) with WhichSideContainsVar var (e2 == e3)
  ... | Left = (e2 == e3) And (ReplaceInCnd k var (plus e1 (const 1)) ((minus e2 (const 1)) < e3))
  ... | Right = (e2 == e3) And (ReplaceInCnd k var (plus e1 (const 1)) (e2 > (minus e3 (const 1)))) --trust me this works
  ... | NoSide = (e2 == e3)
  ModifyCnd (VarRstr k var ">" e1) (e2 > e3) with WhichSideContainsVar var (e2 > e3)
  ... | Left = (e2 > e3) Or (ReplaceInCnd k var (plus e1 (const 1)) (e2 > e3))
  ... | Right = (e2 > e3) And (ReplaceInCnd k var (plus e1 (const 1)) (e2 > e3))
  ... | NoSide = (e2 > e3)
  ModifyCnd (VarRstr k var ">" e1) (e2 < e3) with WhichSideContainsVar var (e2 < e3)
  ... | Left = (e2 < e3) And (ReplaceInCnd k var (plus e1 (const 1)) (e2 < e3))
  ... | Right = (e2 < e3) Or (ReplaceInCnd k var (plus e1 (const 1)) (e2 < e3))
  ... | NoSide = (e2 < e3)
  ModifyCnd vr c = c --I don't even know what these other cases are, but I don't want to touch them
  

  --Will return false if there is any state from the Disj in which Cnd does not hold, and true otherwise
  --This is where the AllStates([s])/NoState thing kinda breaks down, since everywhere else it makes since, I think,
  --To attach state restrictions to [s] (if a program gets the set of all states, and assigns x=3, it just attaches
  --That restriction to [s]), but now, it would make more sense to have VarRstr :S: NoState, since we are checking
  --for states which violate the Cnd, which NoState will never do, and [s] will most often do
  --The idea here is that state restrictions are consumed and used to modify the condition until we reach the [s] case,
  --Where the condition will now read as AlwaysTrue if the it met the restrictions (eg, rstr x =4, cnd x < 5 becomes cnd 4 < 5, reads as AlwaysTrue)
  {-# TERMINATING #-}
  StDisjSatisfiesCnd : StateDisj → Cnd → Bool
  StDisjSatisfiesCnd (Only NoState) c = true
  StDisjSatisfiesCnd (Only [s]) c = AlwaysTrue c
  StDisjSatisfiesCnd (st1 StOr st2) c =  boolOr (StDisjSatisfiesCnd (Only st1) c) (StDisjSatisfiesCnd st2 c)
  StDisjSatisfiesCnd (Only (vr :S: states)) c = StDisjSatisfiesCnd (Only states) (ModifyCnd vr c)
  
  

  --An object which provides evidence that the predicate holds in all states in the state set
  data ConditionHolds : StateDisj → Cnd → Set where
    ConditionHoldsProof : ∀ {st : StateDisj} {c : Cnd}
      → (StDisjSatisfiesCnd st c ≡ true)
      -----------------------------
      → ConditionHolds st c

{- --Assumes c1 and c2 are in canonical form (canonicalization function not yet written)
  data HoareTripleStateSet : Cnd → Stmt → Cnd → Set where
    HTStateSetProof : ∀ {c1 c2 : Cnd} {s : Stmt}
      → (ConditionHolds (ExecStateSet (StatesSatisfying c1) s) c2)
      ---------------------------
      → HoareTripleStateSet c1 s c2
-}
