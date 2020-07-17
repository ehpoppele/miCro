module Interpreter.HoareTriples where

  open import Interpreter.miCro
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


--- Condition Functions! ---
---This all assumes conditions are in a canonical form, without Not and with Or on the outermost level only; also Or should be x Or (y Or ...)
---Canonical Form also assumes all comparisons have one side with a single variable (and mult by const; by 1 at minimum); not sure how this would work out...
---Also need the forms to have EVERY variable multiplied by a const (so add times 1 where needed) as this makes later work easier

{- will take a Cnd to which a NOT was attached and simplify so the NOT can be removed
  CndFlip : Cnd → Cnd
  CndFlip -}

  --This will need an overhaul soon
  AlwaysTrue : Cnd → Bool
  AlwaysTrue (cndBool true) = true
  AlwaysTrue (cndBool false) = false
  AlwaysTrue (c1 Or c2) = boolOr (AlwaysTrue c1) (AlwaysTrue c2)
  AlwaysTrue (c1 And c2) = boolAnd (AlwaysTrue c1) (AlwaysTrue c2)
  AlwaysTrue (Not c) with AlwaysTrue c --Don't have a boolNot function implemented yet; maybe should do that
  ... | true = false
  ... | false = true
  AlwaysTrue ((readVar str1) == (readVar str2)) = primStringEquality str1 str2 --need to add more stuff here
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
  ReplaceInExp n var e1 (readVar str) = times e1 n
  ReplaceInExp n var e1 (plus e2 e3) = plus (ReplaceInExp n var e1 e2) (ReplaceInExp n var e1 e3)
  ReplaceInExp n var e1 (minus e2 e3) = minus (ReplaceInExp n var e1 e2) (ReplaceInExp n var e1 e3)
  ReplaceInExp n var e1 (times e2 n2) = times (ReplaceInExp n var e1 e2) n2
  ReplaceInExp n var e1 e2 = e2 --All that remains are illegal heap ops, deprecated readVar++, and const 

  -- If string is a variable in Cnd, this multiplies the Cnd (assumed to be a comp)
  -- By nat, then replaces all instances of nat*var in Cnd with exp, and returns that Cnd 
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
  ... | Left = (e2 == e3) Or (ReplaceInCnd k var (minus e1 (const 1)) ((plus e2 (const 1)) > e3))
  ... | Right = (e2 == e3) And (ReplaceInCnd k var (minus e1 (const 1)) (e2 < (plus e3 (const 1)))) --trust me this works
  ... | NoSide = (e2 == e3)
  ModifyCnd (VarRstr k var "<" e1) c with WhichSideContainsVar var c
  ... | Left = c 
  ... | Right = c
  ... | NoSide = c
  ModifyCnd (VarRstr k var ">" e1) c with WhichSideContainsVar var c
  ... | Left = c
  ... | Right = c
  ... | NoSide = c
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
