module Semantics.ExpTests where

    open import Language.miCro
    open import Language.miCro_parser --need the pair type
    open import Semantics.Expressions
    import Relation.Binary.PropositionalEquality as Eq
    open import Agda.Builtin.Bool
    open Eq using (_≡_; refl)
    open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

    -- Tests for the canonical form function --

    -- First expression is (3x - 4*5) + 5*(y - 2x), should canonicalize to 5y - (7x + 20)
    Exp1 = plus (minus (times (readVar "x") 3) (times (const 5) 4)) (times (minus (readVar "y") (times (readVar "x") 2)) 5)

    TestExp1 : (CFExp Exp1) ≡ minus (times (readVar "y") 5) (plus (times (readVar "x") 7) (const 20))
    TestExp1 = refl

    -- Exp2 is a rewrite of the first expression, so that we can test for equality, in this case is (2x - 4x) - 5((x + 4) - y)
    Exp2 = minus (minus (times (readVar "x") 2) (times (readVar "x") 4)) (times (minus (plus (readVar "x") (const 4)) (readVar "y")) 5)

    TestExp2 : (CFExp Exp2) ≡ minus (times (readVar "y") 5) (plus (times (readVar "x") 7) (const 20))
    TestExp2 = refl

    TestExp1=2 : ExpEquality (CFExp Exp1) (CFExp Exp2) ≡ true
    TestExp1=2 = refl

    -- Exp 3 is 6(y-(x+3))-2, should canonicalize to 6y - (6x + 20)
    Exp3 = minus (times (minus (readVar "y") (plus (readVar "x") (const 3))) 6) (const 2)

    TestExp3 : (CFExp Exp3) ≡ (minus (times (readVar "y") 6) (plus (times (readVar "x") 6) (const 20)))
    TestExp3 = refl

    --Exp 4 is (0 - 7x) + (7(y-3) + 1), CF is 7y - 7x + 20
    Exp4  = plus (minus (const 0) (times (readVar "x") 7)) (plus (times (minus (readVar "y") (const 3)) 7) (const 1))

    TestExp4 : (CFExp Exp4) ≡ (minus (times (readVar "y") 7) (plus (times (readVar "x") 7) (const 20)))
    TestExp4 = refl

    Test1<3 : ExpLessThan (CFExp Exp1) (CFExp Exp3) ≡ true
    Test1<3 = refl

    Test1<4 : ExpLessThan (CFExp Exp1) (CFExp Exp4) ≡ true
    Test1<4 = refl

    -- This last pair should fail since we can't decide anything about the values of x and y
    Test3<4 : ExpLessThan (CFExp Exp3) (CFExp Exp4) ≡ false
    Test3<4 = refl
    Test4<3 : ExpLessThan (CFExp Exp3) (CFExp Exp4) ≡ false
    Test4<3 = refl

    --Exp-ception
    TestExpRep : (ReplaceInExp 7 "x" (minus (times (readVar "y") 7) (plus (times (readVar "x") 7) (const 20)))(minus (times (readVar "y") 7) (plus (times (readVar "x") 7) (const 20)))) ≡ (minus (times (readVar "y") 7) (plus (minus (times (readVar "y") 7) (plus (times (readVar "x") 7) (const 20))) (const 20)))
    TestExpRep = refl
