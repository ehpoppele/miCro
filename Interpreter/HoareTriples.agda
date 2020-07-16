module Interpreter.HoareTriples where

  open import Interpreter.miCro
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open import Agda.Builtin.Bool

  data evalsTo : RAM → Exp → Nat → Set where
    evalsTrue : ∀ {m : RAM} {x : Exp} {n : Nat}
      → (eval m x) ≡ n
      ------------
      → evalsTo m x n

  basicEval : evalsTo ([e] & [h]) (readVar "x") zero
  basicEval = evalsTrue refl

  --Change checks to to checks true?
  data checksTo : RAM → Cnd → Bool → Set where
    checksOut : ∀ {m : RAM} {c : Cnd} {b : Bool}
      → (check m c) ≡ b
      -------------------
      → checksTo m c b

  basicCheck : checksTo ([e] & [h]) ((readVar "x") <= (const 1)) true
  basicCheck = checksOut refl

  data execsTo : RAM → Stmt → RAM → Set where
    execsCorrect : ∀ {m1 m2 : RAM} {s : Stmt}
      → (exec m1 s) ≡ m2
      ----------------------------
      → execsTo m1 s m2

  basicExec : execsTo ([e] & [h]) (If ((readVar "X") == (const 0)) (AssignVar "X" (plus (readVar "X") (const 1)))) (((Var "X" 1) :e: [e])& [h])
  basicExec = execsCorrect refl

------------------------------------

  data VarRestriction : Set where
    VarRstr : String → String → Exp → VarRestriction --Could clean this up; for now it's varName → ComparisonString → thing compared to. Maybe make comparisons a distinct thing/subset of Cnd?

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
---Canonical Form also assumes all comparisons have one side with a single variable; not sure how this would work out...

{- will take a Cnd to which a NOT was attached and simplify so the NOT can be removed
  CndFlip : Cnd → Cnd
  CndFlip -}

  --This will need an overhaul when I add more functions depending on how C. forms look like 
  AlwaysTrue : Cnd → Bool
  AlwaysTrue (cndBool true) = true
  AlwaysTrue (cndBool false) = false
  AlwaysTrue (c1 Or c2) = boolOr (AlwaysTrue c1) (AlwaysTrue c2)
  AlwaysTrue (c1 And c2) = boolAnd (AlwaysTrue c1) (AlwaysTrue c2)
  AlwaysTrue (Not c) with AlwaysTrue c --Don't have a boolNot function implemented yet; maybe should do that
  ... | true = false
  ... | false = true
  AlwaysTrue ((readVar str1) == (readVar str2)) = primStringEquality str1 str2
  AlwaysTrue other = false --Other comparisons currently not allowed, so get outta here

--Finds state sets complying with the given non-Or condition
  FindStates : Cnd → StateSet
  FindStates (cndBool true) = [s]
  FindStates (cndBool false) = NoState
  FindStates (c1 And c2) = StateJoin (FindStates c1) (FindStates c2)
  FindStates ((readVar str) == e) = (VarRstr str "==" e) :S: [s]
  FindStates ((readVar str) < e) = (VarRstr str "<" e) :S: [s]
  FindStates other = NoState --Currently not allowing any other conditions to keep it simple

--Finds state sets complying with the given condition; handles Or then passes off the rest
  StatesSatisfying : Cnd → StateDisj
  StatesSatisfying (c1 Or c2) = (FindStates c1) StOr (StatesSatisfying c2)
  StatesSatisfying c = Only (FindStates c)

  --Will return false if there is any state from the Disj in which Cnd does not hold, and true otherwise
  {-# TERMINATING #-}
  SatisfiesPredicate : StateDisj → Cnd → Bool
  SatisfiesPredicate (Only NoState) c = true
  SatisfiesPredicate (Only [s]) c = AlwaysTrue c
  SatisfiesPredicate (st1 StOr st2) c =  boolOr (SatisfiesPredicate (Only st1) c) (SatisfiesPredicate st2 c)
  SatisfiesPredicate (Only ((VarRstr var "<" exp) :S: StSet)) c =
  SatisfiesPredicate (Only (
  
  

  --An object which provides evidence that the predicate holds in all states in the state set
  data PredicateHolds : StateDisj → Cnd → Set where
    PredicateHoldsProof : ∀ {st : StateDisj} {c : Cnd}
      → (SatisfiesPredicate st c ≡ true)
      -----------------------------
      → PredicateHolds st c

{-
  data HoareTripleStateSet : Cnd → Stmt → Cnd → Set where
    HTStateSetProof : ∀ {c1 c2 : Cnd} {s : Stmt}
      → (PredicateHolds (ExecStateSet (StatesSatisfying c1) s) c2)
      ---------------------------
      → HoareTripleStateSet c1 s c2
-}
