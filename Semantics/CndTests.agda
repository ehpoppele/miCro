--Testing for canonical forms of conditions; used mostly for debugging
module Semantics.CndTests where

    open import Semantics.Conditions
    open import Language.miCro
    open import Language.miCro_parser
    open import Semantics.Expressions
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl)
    open import Agda.Builtin.Bool
    open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

    --First condition is (x <= 3) And (4 >= 4), should canonicalize to (1x < 3) Or (1x == 3)
    Cnd1 = ((readVar "x") <= (const 3)) And ((const 4) >= (const 4))

    CndTest1 : (CFCnd Cnd1) ≡ ((times (readVar "x") 1) < (const 3)) Or ((times (readVar "x") 1) == (const 3))
    CndTest1 =
      begin
        (CFCnd Cnd1)
      ≡⟨⟩
        (ApplyBools (CFCLinMain (CndFilterAnds (CndSplitComparisons (ApplyNots (CCToBool (CndFixExp Cnd1)))))))
      ≡⟨⟩
        (ApplyBools (CFCLinMain (CndFilterAnds (CndSplitComparisons (ApplyNots (CCToBool (((times (readVar "x") 1) <= (const 3)) And ((const 4) >= (const 4)))))))))
      ≡⟨⟩
        (ApplyBools (CFCLinMain (CndFilterAnds (CndSplitComparisons (ApplyNots (((times (readVar "x") 1) <= (const 3)) And (cndBool true)) )))))
      ≡⟨⟩
        (ApplyBools (CFCLinMain (CndFilterAnds (CndSplitComparisons (((times (readVar "x") 1) <= (const 3)) And (cndBool true))))))
      ≡⟨⟩
        (ApplyBools (CFCLinMain (CndFilterAnds ((((times (readVar "x") 1) < (const 3)) Or ((times (readVar "x") 1) == (const 3))) And (cndBool true)))))
      ≡⟨⟩
        (ApplyBools (CFCLinMain ((((times (readVar "x") 1) < (const 3)) And (cndBool true))  Or (((times (readVar "x") 1) == (const 3)) And (cndBool true))) ))
      ≡⟨⟩
        (ApplyBools (((cndBool true) And (((times (readVar "x") 1) < (const 3)) And (cndBool true))) Or ((cndBool true) And (((times (readVar "x") 1) == (const 3)) And (cndBool true)))) )
      ≡⟨⟩
        ((times (readVar "x") 1) < (const 3)) Or ((times (readVar "x") 1) == (const 3))
      ∎

    CndTest1Refl : (CFCnd Cnd1) ≡ ((times (readVar "x") 1) < (const 3)) Or ((times (readVar "x") 1) == (const 3))
    CndTest1Refl = refl

    --Second Condition is ((5 > 3x + y) Or (6 > 2y)) And (x > 4), should go to ? (3x < 5 - y And x > 4) Or (2y < 6 And x > 4)
    Cnd2 = ((((const 5) > (plus (times (readVar "x") 3) (readVar "y"))) Or ((const 6) > (times (readVar "y") 2))) And ((readVar "x") > (const 4)))

    --Step-by-step proof of canonicalization that was used for debugging
    CndTest2 : (CFCnd Cnd2) ≡ ((((times (readVar "x") 1) > (const 4)) And ((times (readVar "x") 3) < (minus (const 5) (times (readVar "y") 1)))) Or (((times (readVar "x") 1) > (const 4)) And ((times (readVar "y") 2) < (const 6))))
    CndTest2 =
      begin
        CFCnd Cnd2
      ≡⟨⟩
        (ApplyBools (CFCLinMain (CndFilterAnds (CndSplitComparisons (ApplyNots (CCToBool (CndFixExp Cnd2)))))))
      ≡⟨⟩
        (ApplyBools (CFCLinMain (CndFilterAnds (CndSplitComparisons (ApplyNots (CCToBool (CndFixExp ((((const 5) > (plus (times (readVar "x") 3) (readVar "y"))) Or ((const 6) > (times (readVar "y") 2))) And ((readVar "x") > (const 4)))  )))))))
      ≡⟨⟩
        (ApplyBools (CFCLinMain (CndFilterAnds (CndSplitComparisons (ApplyNots (CCToBool ((((times (readVar "x") 3) < (minus (const 5) (times (readVar "y") 1))) Or ((times (readVar "y") 2) < (const 6))) And ((times (readVar "x") 1) > (const 4)))  ))))))
      ≡⟨⟩
        (ApplyBools (CFCLinMain (CndFilterAnds (CndSplitComparisons (ApplyNots ((((times (readVar "x") 3) < (minus (const 5) (times (readVar "y") 1))) Or ((times (readVar "y") 2) < (const 6))) And ((times (readVar "x") 1) > (const 4)))  )))))
      ≡⟨⟩
        (ApplyBools (CFCLinMain (CndFilterAnds (CndSplitComparisons ((((times (readVar "x") 3) < (minus (const 5) (times (readVar "y") 1))) Or ((times (readVar "y") 2) < (const 6))) And ((times (readVar "x") 1) > (const 4)))  ))))
      ≡⟨⟩
        (ApplyBools (CFCLinMain (CndFilterAnds ((((times (readVar "x") 3) < (minus (const 5) (times (readVar "y") 1))) Or ((times (readVar "y") 2) < (const 6))) And ((times (readVar "x") 1) > (const 4)))  )))
      ≡⟨⟩
        (ApplyBools (CFCLinMain ((((times (readVar "x") 3) < (minus (const 5) (times (readVar "y") 1))) And ((times (readVar "x") 1) > (const 4))) Or (((times (readVar "y") 2) < (const 6)) And ((times (readVar "x") 1) > (const 4)))) ))
      ≡⟨⟩
        (ApplyBools (((times (readVar "x") 1 > const 4) And  ((times (readVar "x") 3 < minus (const 5) (times (readVar "y") 1)) And cndBool true)) Or ((times (readVar "x") 1 > const 4) And ((times (readVar "y") 2 < const 6) And cndBool true))) )
      ≡⟨⟩
        ((((times (readVar "x") 1) > (const 4)) And ((times (readVar "x") 3) < (minus (const 5) (times (readVar "y") 1)))) Or (((times (readVar "x") 1) > (const 4)) And ((times (readVar "y") 2) < (const 6))))
      ∎

    CndTest2Refl : (CFCnd Cnd2) ≡ ((((times (readVar "x") 1) > (const 4)) And ((times (readVar "x") 3) < (minus (const 5) (times (readVar "y") 1)))) Or (((times (readVar "x") 1) > (const 4)) And ((times (readVar "y") 2) < (const 6))))
    CndTest2Refl = refl
