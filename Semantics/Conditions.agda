--Functions for conditions and their use in the Hoare Triples
--Primarily the failed canonicalization function, which I believe works
--Except for its ability to reduce set of comparisons on variables to true or false when appropriate
--This ultimately would require some function that could solve equations and inequalities
--Also contains some functions to find variables in conditions, and the AlwaysTrue function
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
    AlwaysTrue (e1 != e2) with ExpEquality (CFExp e1) (CFExp e2)
    ... | true = false
    ... | false = true
    AlwaysTrue (e1 < e2) = ExpLessThan (CFExp e1) (CFExp e2)
    AlwaysTrue (e1 > e2) = ExpLessThan (CFExp e2) (CFExp e1)
    AlwaysTrue (e1 >= e2) = boolOr (ExpLessThan (CFExp e2) (CFExp e1)) (ExpEquality (CFExp e1) (CFExp e2))
    AlwaysTrue (e1 <= e2) = boolOr (ExpLessThan (CFExp e1) (CFExp e2)) (ExpEquality (CFExp e1) (CFExp e2))

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

    --Used for the function below, identifying where a variable appears in a comparison, or if it is not present
    data Side : Set where
      Left : Side
      Right : Side
      NoSide : Side --This should've just been "NotFound" or "NotPresent"

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
    ReplaceInCnd : Nat → String → Exp → Cnd → Cnd
    ReplaceInCnd n var e1 (e2 == e3) with boolOr (ExpContainsVar var e2) (ExpContainsVar var e3)
    ... | true = (ReplaceInExp n var e1 (CTimes e2 n)) == (ReplaceInExp n var e1 (CTimes e3 n))
    ... | false = (e2 == e3)
    ReplaceInCnd n var e1 (e2 < e3) with boolOr (ExpContainsVar var e2) (ExpContainsVar var e3)
    ... | true = (ReplaceInExp n var e1 (CTimes e2 n)) < (ReplaceInExp n var e1 (CTimes e3 n))
    ... | false = (e2 < e3)
    ReplaceInCnd n var e1 (e2 > e3) with boolOr (ExpContainsVar var e2) (ExpContainsVar var e3)
    ... | true = (ReplaceInExp n var e1 (CTimes e2 n)) > (ReplaceInExp n var e1 (CTimes e3 n))
    ... | false = (e2 > e3)
    ReplaceInCnd n var e1 (e2 != e3) with boolOr (ExpContainsVar var e2) (ExpContainsVar var e3)
    ... | true = (ReplaceInExp n var e1 (CTimes e2 n)) != (ReplaceInExp n var e1 (CTimes e3 n))
    ... | false = (e2 != e3)
    ReplaceInCnd n var e otherCnd = cndBool false --Need to finish this?

    --Rewrites comparisons so that expressions are in canonical form
    --And also so there is a single positive var on the left hand side (when possible)
    --Makes calls to a function in the Expressions file (CFComparison, for "Canonical Form" of a comparison)
    --Since that function deals pretty much only with expressions, it seemed appropriate to put it there
    CndFixExp : Cnd → Cnd
    CndFixExp (c1 Or c2) = (CndFixExp c1) Or (CndFixExp c2)
    CndFixExp (c1 And c2) = (CndFixExp c1) And (CndFixExp c2)
    CndFixExp (Not c) = Not (CndFixExp c)
    CndFixExp (cndBool b) = (cndBool b)
    CndFixExp (e1 == e2) with (CFComparison e1 e2)
    ... | Same (e1' × e2') = e1' == e2'
    ... | Flipped (e1' × e2') = e1' == e2'
    CndFixExp (e1 < e2) with (CFComparison e1 e2)
    ... | Same (e1' × e2') = e1' < e2'
    ... | Flipped (e1' × e2') = e1' > e2'
    CndFixExp (e1 <= e2) with (CFComparison e1 e2)
    ... | Same (e1' × e2') = e1' <= e2'
    ... | Flipped (e1' × e2') = e1' >= e2'
    CndFixExp (e1 > e2) with (CFComparison e2 e1)
    ... | Same (e1' × e2') = e1' < e2'
    ... | Flipped (e1' × e2') = e1' > e2'
    CndFixExp (e1 >= e2) with (CFComparison e2 e1)
    ... | Same (e1' × e2') = e1' <= e2'
    ... | Flipped (e1' × e2') = e1' >= e2'
    CndFixExp (e1 != e2) with (CFComparison e1 e2)
    ... | Same (e1' × e2') = e1' != e2'
    ... | Flipped (e1' × e2') = e1' != e2'

    --Reduces all Const-Only comparisons in a Cnd to Bools
    CCToBool : Cnd → Cnd
    CCToBool (c1 Or c2) = ((CCToBool c1) Or (CCToBool c2))
    CCToBool (c1 And c2) = ((CCToBool c1) And (CCToBool c2))
    CCToBool (Not c1) = Not (CCToBool c1)
    CCToBool ((const n) == (const m)) = (cndBool (AlwaysTrue ((const n) == (const m))))
    CCToBool ((const n) < (const m)) = (cndBool (AlwaysTrue ((const n) < (const m))))
    CCToBool ((const n) <= (const m)) = (cndBool (AlwaysTrue ((const n) <= (const m))))
    CCToBool ((const n) > (const m)) = (cndBool (AlwaysTrue ((const n) > (const m))))
    CCToBool ((const n) >= (const m)) = (cndBool (AlwaysTrue ((const n) >= (const m))))
    CCToBool ((const n) != (const m)) = (cndBool (AlwaysTrue ((const n) != (const m))))
    CCToBool (e < (const zero)) = cndBool false --This rule needs to be somewhere in the canonicalization process, so I put it here
    CCToBool c = c

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

    {- Incomplete functions that would reduce groups of comparisons to bools when possible
    -- These would reduce comparisons joined by And to false if they were inconsistent with each other
    -- And those joined by Or to true when they combined to allow all possible values for a variable (eg x < 4 Or x == 5 Or x > 6)
    -- Not used because of the difficulty on And on two equalities; if we have x == e1 And x == e2 we need to check if the equation 0 = e1 - e2
    -- Has any possible solutions; I believe such a solver is outside the scope of this project.

    --Iterates over each comparison in c2 and combines it with c1 when possible
    --Assumes c1 is a comparison and returns the modified version of c1 and c2
    CndCombineAndHelper : Cnd → (Pair Cnd Cnd)
    CndCombineAndHelper 

    --Combines the comparisons in an And chain; removes redundant comparisons and replaces incompatible ones with False
    CndCombineAnd : Cnd → Cnd
    CndCombineAnd (c1 And c2) = let c2' = (CndCombineAnd c2) in let (c1'' × c2'') = (CndCombineAndHelper c1 c2') in (c1'' And c2'')
    CndCombineAnd (Not c) = Not (CndCombineAnd c)
    CndCombineAnd (c1 Or c2) = (CndCombineAnd c1) Or (CndCombineAnd c2)
    CndCombineAnd c = c

    --Combines comparisons before they are split so that which are Always or Never True can be found
    --We can assume the nots are gone by now, I hope
    CndCombineComparisons : Cnd → Cnd
    CndCombineComparisons (Not c) = Not (CndCombineComparisons) --still writing it out since we need to have a not rule for the function to be complete
    CndCombineComparisons (c1 And c2) = CndCombineAnd (c1 And c2)
    CndCombineComparisons (c1 Or c2)
    ... | 
    -}

    --Split any <=/>= comparisons into an Or between == and </>
    --Honestly I don't know why I'm still doing this, since my decision to remove all =</>= from CForms doesn't really have a good basis in anything
    CndSplitComparisons : Cnd → Cnd
    CndSplitComparisons (c1 Or c2) = (CndSplitComparisons c1) Or (CndSplitComparisons c2)
    CndSplitComparisons (c1 And c2) = (CndSplitComparisons c1) And (CndSplitComparisons c2)
    CndSplitComparisons (e1 <= e2) = (e1 < e2) Or (e1 == e2)
    CndSplitComparisons (e1 >= e2) = (e1 > e2) Or (e1 == e2)
    CndSplitComparisons c = c

    --Mutually recursize pair functions which "push" Ands down to the lower level so that only Or is at the top level
    --Now I'm unsure of when the Ors get linearized? but this just sorts the two, while later functions linearize things
    FilterAndsHelper : Cnd → Cnd → Cnd
    CndFilterAnds : Cnd → Cnd

    --Gets passed two conditions; does filtering work on the second and then joins the first to that in a manner depending on the result
    --Based on its use in the main filtering function, the first Cnd should always be an And
    FilterAndsHelper (c1 And c2) c3 with CndFilterAnds c3
    ... | (c3' And c4') = ((c1 And c2) And (c3' And c4'))
    ... | (c3' Or c4') = (CndFilterAnds ((c1 And c2) And c3')) Or (CndFilterAnds ((c1 And c2) And c4'))
    ... | c3' = (c1 And c2) And c3'
    FilterAndsHelper c1 c2 = c1 And c2 --Should never get here
    

    --Takes a Cnd and makes sure all the Ands are at a lower level than all the Ors
    --So that Ands only join atomic Cnds or other Ands (assuming Nots are gone by now)
    CndFilterAnds (c1 Or c2) = (CndFilterAnds c1) Or (CndFilterAnds c2)
    CndFilterAnds ((c1 Or c2) And c3) = (CndFilterAnds (c1 And c3)) Or (CndFilterAnds (c2 And c3))
    CndFilterAnds (c1 And (c2 Or c3)) = (CndFilterAnds (c1 And c2)) Or (CndFilterAnds (c1 And c3))
    CndFilterAnds ((c1 And c2) And c3) with CndFilterAnds (c1 And c2)
    ... | (c1' And c2') = FilterAndsHelper (c1' And c2') c3 --We will only get an And back if both c's are comparisons or ands between comparisons
    ... | (c1' Or c2') = CndFilterAnds ((c1' Or c2') And c3)
    ... | c = c
    CndFilterAnds (c1 And (c2 And c3)) with CndFilterAnds (c2 And c3)
    ... | (c2' And c3') = FilterAndsHelper (c2' And c3') c1
    ... | (c2' Or c3') = CndFilterAnds (c1 And (c2' Or c3'))
    ... | c = c
    CndFilterAnds (comp1 And comp2) = (comp1 And comp2)
    CndFilterAnds comparison = comparison --Nots should be gone, so these will be unchanged

    --Helper Linearization function; takes the first argument as the chain so far and the second as rest that must be added
    CFCLinearize : Cnd → Cnd → Cnd
    CFCLinearize c ((c1 And c2) And c3) = CFCLinearize c (c1 And (c2 And c3))
    CFCLinearize c (c1 And c2) = CFCLinearize (c1 And c) c2 --We can assume c1 here is atomic
    CFCLinearize c c1 = c1 And c
    

    --Main linearize function for conditions; skips over Ors and makes calls to the working Lin function when necessary
    --Will convert all the Ands to a strict linear form (atomic And (atomic And ...)) instead of tree form (... And ...) And (.. And ...)
    CFCLinMain : Cnd → Cnd
    CFCLinMain (c1 Or c2) = (CFCLinMain c1) Or (CFCLinMain c2)
    CFCLinMain (c1 And c2) = CFCLinearize (cndBool true) (c1 And c2) --we give a True to start off the and chain, which can be removed later
    CFCLinMain c = c

    --Applies and simplifies all cndBools, so that true And c goes to c, false and c goes to false, etc
    ApplyBools : Cnd → Cnd
    ApplyBools ((cndBool true) Or c) = cndBool true
    ApplyBools (c Or (cndBool true)) = cndBool true
    ApplyBools ((cndBool false) Or c) = ApplyBools c
    ApplyBools (c Or (cndBool false)) = ApplyBools c
    ApplyBools ((cndBool true) And c) = ApplyBools c
    ApplyBools (c And (cndBool true)) = ApplyBools c
    ApplyBools ((cndBool false) And c) = cndBool false
    ApplyBools (c And (cndBool false)) = cndBool false
    ApplyBools (c1 Or c2) with ((ApplyBools c1) Or (ApplyBools c2))
    ... | ((cndBool b) Or c2') = ApplyBools ((cndBool b) Or c2')
    ... | (c1' Or (cndBool b)) = ApplyBools (c1' Or (cndBool b))
    ... | c = c
    ApplyBools (c1 And c2) with ((ApplyBools c1) And (ApplyBools c2))
    ... | ((cndBool b) And c2') = ApplyBools ((cndBool b) And c2')
    ... | (c1' And (cndBool b)) = ApplyBools (c1' And (cndBool b))
    ... | c = c
    ApplyBools c = c
    

    --Canonicalization function, taking a condition to it's canonical form
    --This preserves a tree of ORs at the top level, joining lists of ANDs
    --With all Nots being applied and removed. Similarly, <= and >= are broken into ORs between the two comparisons
    --This first fixes comparisons so they are written in a canonical form, then writes all the const-only comparisons as booleans, then applies the Nots,
    --then it splits all the comparisons that haven't been reduced to bools since it's too late to change my canonical form
    --Not allowing <= even though I realize that doesn't make much sense, after that the function will
    --then "filter down" the Ands, and then finally it ensures all Cnds joined by ands are in a list (rather than tree) form
    --And then Another step to remove/reduce boolCnds
    --I think this is missing a step to linearize Ors; not needed for my current code but would be to ensure that all
    --equivalent Cnds have the same CForm
    --Of course, this is also missing the step to reduce comparison groups to bools when applicable (eg, x < 5 AND x > 6 should become false)
    --But that requires finding whether a systems of equations has no solutions or if all values are solutions, and
    --such an algorithm would require work beyond the scope of this project

    CFCnd : Cnd → Cnd
    CFCnd c = ApplyBools (CFCLinMain (CndFilterAnds (CndSplitComparisons (ApplyNots (CCToBool (CndFixExp c))))))
