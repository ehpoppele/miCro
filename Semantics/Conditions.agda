module Semantics.Conditions where

    open import Language.miCro
    open import Language.miCro_parser
    open import Semantics.Expressions
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl)
    open import Agda.Builtin.Bool

    --Most functions in this file assume that the condition being used is in canonical form

    --Returns whether or not a given condition is always true, regardless of the possible values of any variables included
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

    --Checks to see if the condition contains the given variable
    --NOTE: currently this assumes the condition is a comparison; it will not break down and/or/etc.
    CndContainsVar : String → Cnd → Bool
    CndContainsVar var (e1 == e2) = boolOr (ExpContainsVar var e1) (ExpContainsVar var e2)
    CndContainsVar var (e1 <= e2) = boolOr (ExpContainsVar var e1) (ExpContainsVar var e2)
    CndContainsVar var (e1 >= e2) = boolOr (ExpContainsVar var e1) (ExpContainsVar var e2)
    CndContainsVar var (e1 != e2) = boolOr (ExpContainsVar var e1) (ExpContainsVar var e2)
    CndContainsVar var (e1 < e2) = boolOr (ExpContainsVar var e1) (ExpContainsVar var e2)
    CndContainsVar var (e1 > e2) = boolOr (ExpContainsVar var e1) (ExpContainsVar var e2)
    CndContainsVar var c = false

    data Side : Set where
      Left : Side
      Right : Side
      NoSide : Side

    --Extra containment function, returning Left Right or NoSide, for what part of a comp Cnd contains the var
    --Could modify some things to have this replace CndContainsVar later
    WhichSideContainsVar : String → Cnd → Side
    WhichSideContainsVar var (e1 == e2) = boolIfElse (ExpContainsVar var e1) (Left) (boolIfElse (ExpContainsVar var e2) (Right) (NoSide))
    WhichSideContainsVar var (e1 <= e2) = boolIfElse (ExpContainsVar var e1) (Left) (boolIfElse (ExpContainsVar var e2) (Right) (NoSide))
    WhichSideContainsVar var (e1 >= e2) = boolIfElse (ExpContainsVar var e1) (Left) (boolIfElse (ExpContainsVar var e2) (Right) (NoSide))
    WhichSideContainsVar var (e1 != e2) = boolIfElse (ExpContainsVar var e1) (Left) (boolIfElse (ExpContainsVar var e2) (Right) (NoSide))
    WhichSideContainsVar var (e1 < e2) = boolIfElse (ExpContainsVar var e1) (Left) (boolIfElse (ExpContainsVar var e2) (Right) (NoSide))
    WhichSideContainsVar var (e1 > e2) = boolIfElse (ExpContainsVar var e1) (Left) (boolIfElse (ExpContainsVar var e2) (Right) (NoSide))
    WhichSideContainsVar var c = NoSide --this function only accepts comparisons conditions, so the rest are disregarded

    -- If string is a variable in Cnd, this multiplies the Cnd (assumed to be a comp)
    -- By nat, then replaces all instances of nat*var in Cnd with exp, and returns that Cnd
    --- !!!!! Need to fix this; change so that instead of times its a "canonical times" that pushes the times down to the "lowest level" (closest to the variables/consts)
    ReplaceInCnd : Nat → String → Exp → Cnd → Cnd
    ReplaceInCnd n var e1 (e2 == e3) with boolOr (ExpContainsVar var e2) (ExpContainsVar var e3)
    ... | true = (ReplaceInExp n var e1 (times e2 n)) == (ReplaceInExp n var e1 (times e3 n))
    ... | false = (e2 == e3)
    ReplaceInCnd n var e1 (e2 < e3) with boolOr (ExpContainsVar var e2) (ExpContainsVar var e3)
    ... | true = (ReplaceInExp n var e1 (times e2 n)) < (ReplaceInExp n var e1 (times e3 n))
    ... | false = (e2 < e3)
    ReplaceInCnd n var e1 (e2 > e3) with boolOr (ExpContainsVar var e2) (ExpContainsVar var e3)
    ... | true = (ReplaceInExp n var e1 (times e2 n)) > (ReplaceInExp n var e1 (times e3 n))
    ... | false = (e2 > e3)
    ReplaceInCnd n var e1 (e2 != e3) with boolOr (ExpContainsVar var e2) (ExpContainsVar var e3)
    ... | true = (ReplaceInExp n var e1 (times e2 n)) != (ReplaceInExp n var e1 (times e3 n))
    ... | false = (e2 != e3)
    ReplaceInCnd n var e otherCnd = cndBool false --Need to finish this?

    --Returns an "opposite" Cnd; the result of applying a Not to the given condition
    FlipCnd : Cnd → Cnd
    FlipCnd (Not c) = c
    FlipCnd (cndBool true) = (cndBool false)
    FlipCnd (cndBool false) = (cndBool true)
    FlipCnd (c1 And c2) = (FlipCnd c1) Or (FlipCnd c2)
    FlipCnd (c1 Or c2) = (FlipCnd c1) And (FlipCnd c2)
    FlipCnd (e1 < e2) = (e1 > e2) Or (e1 == e2)
    FlipCnd (e1 <= e2) = (e1 > e2)
    FlipCnd (e1 > e2) = (e1 < e2) Or (e1 == e2)
    FlipCnd (e1 >= e2) = (e1 < e2)
    FlipCnd (e1 == e2) = (e1 != e2)
    FlipCnd (e1 != e2) = (e1 == e2)
    

    --Removes any NOTs appearing in the cnd, while changing the Cnd so that it is still equivalent
    ApplyNots : Cnd → Cnd
    ApplyNots (c1 And c2) = (ApplyNots c1) And (ApplyNots c2)
    ApplyNots (c1 Or c2) = (ApplyNots c1) Or (ApplyNots c2)
    ApplyNots (Not c) = FlipCnd (ApplyNots c)
    ApplyNots c = c

    --Split any <=/>= comparisons into an Or between == and </>
    CndSplitComparisons : Cnd → Cnd
    CndSplitComparisons (e1 <= e2) = (e1 < e2) Or (e1 == e2)
    CndSplitComparisons (e1 >= e2) = (e1 > e2) Or (e1 == e2)
    CndSplitComparisons c = c

    --Takes a Cnd and makes sure all the Ands are at a lower level than all the Ors
    --So that Ands only join atomic Cnds or other Ands (assuming Nots are gone by now)
    CndFilterAnds : Cnd → Cnd
    CndFilterAnds (c1 Or c2) = (CndFilterAnds c1) Or (CndFilterAnds c2)
    CndFilterAnds (() And ()) = 
    

    --Canonicalization function, taking a condition to it's canonical form
    --This preserves a tree of ORs at the top level, joining lists of ANDs
    --With all Nots being applied and removed. Similarly, <= and >= are broken into ORs between the two comparisons
    --This first "applies" the nots and removes them, then splits the <=/>= comparisons, then "filters down" the ANDs,
    --and then finally it ensures all Cnds joined by ands are in a list (rather than tree) form
   -- CFCnd : Cnd → Cnd
   -- CFCnd c = CndFilterAnds (CndSplitComparisons (ApplyNots c))
