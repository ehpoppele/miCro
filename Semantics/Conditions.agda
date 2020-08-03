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
    --AlwaysTrue other = false --Other comparisons currently not allowed, so get outta here

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
    CndFixExp (e1 > e2) with (CFComparison e1 e2)
    ... | Same (e1' × e2') = e1' > e2'
    ... | Flipped (e1' × e2') = e1' < e2'
    CndFixExp (e1 >= e2) with (CFComparison e1 e2)
    ... | Same (e1' × e2') = e1' >= e2'
    ... | Flipped (e1' × e2') = e1' <= e2'
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

    --Split any <=/>= comparisons into an Or between == and </>
    CndSplitComparisons : Cnd → Cnd
    CndSplitComparisons (c1 Or c2) = (CndSplitComparisons c1) Or (CndSplitComparisons c2)
    CndSplitComparisons (c1 And c2) = (CndSplitComparisons c1) And (CndSplitComparisons c2)
    CndSplitComparisons (e1 <= e2) = (e1 < e2) Or (e1 == e2)
    CndSplitComparisons (e1 >= e2) = (e1 > e2) Or (e1 == e2)
    CndSplitComparisons c = c

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
    --This first "applies" the nots and removes them, then rewrites comparisons, then reduces const-only comps to bools, then splits the <=/>= comparisons,
    --then "filters down" the Ands, and then finally it ensures all Cnds joined by ands are in a list (rather than tree) form
    --And then Another step to remove/reduce boolCnds
    CFCnd : Cnd → Cnd
    CFCnd c = ApplyBools (CFCLinMain (CndFilterAnds (CndSplitComparisons (ApplyNots (CCToBool (CndFixExp c))))))
