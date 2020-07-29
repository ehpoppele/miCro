module Semantics.Conditions where

    open import Language.miCro
    open import Language.miCro_parser
    open import Semantics.Expressions
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl)
    open import Agda.Builtin.Bool

--- Condition Functions! ---
---This all assumes conditions are in a canonical form, without Not and with Or on the outermost level only; also Or should be x Or (y Or ...)
---Canonical Form also assumes all comparisons have one side with a single variable (and mult by const; by 1 at minimum); not sure how this would work out...
---Also need the forms to have EVERY variable multiplied by a const (so add times 1 where needed) as this makes later work easier

-- Will later separate some of these (those dealing only with Cnds and not states as well) into a separate file
-- That file will hopefully include a canonicalization for conditions

    --This function does things
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
