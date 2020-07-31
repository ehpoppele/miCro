module HoareTripleExamples where

    open import Language.miCro
    open import Language.miCro_parser
    open import Semantics.Expressions
    open import Semantics.Conditions
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl)
    open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
    open import Agda.Builtin.Bool
    open import HoareTriples

    PreFalse1 : SEnvSatisfiesCnd falseS (cndBool true) ≡ true
    PreFalse1 = refl

    PreFalse : HoareTriple (cndBool false) No-op (cndBool true)
    PreFalse = HTSymbolicEnvProof (ConditionHoldsProof PreFalse1)

    --PreFalseGeneral1 : ∀ (s : Stmt) → SEnvSatisfiesCnd (SymbolicExec zero falseS s) (cndBool true) ≡ true
    --PreFalseGeneral1 (AssignVar str e) = refl
    --PreFalseGeneral1 (Seq s1 s2)

    PostTrueHelper : ∀ (state : SymbolicEnv) → SEnvSatisfiesCnd state (cndBool true) ≡ true
    PostTrueHelper falseS = refl
    PostTrueHelper trueS = refl
    --Can't figure out a way to do all the comparisons at once...
    PostTrueHelper (e1 <S e2) = refl
    PostTrueHelper (e1 >S e2) = refl
    PostTrueHelper (e1 <=S e2) = refl
    PostTrueHelper (e1 >=S e2) = refl
    PostTrueHelper (e1 ==S e2) = refl
    PostTrueHelper (e1 !=S e2) = refl
    PostTrueHelper (e1 orS e2) rewrite (PostTrueHelper e1) | (PostTrueHelper e2) = refl
    PostTrueHelper (e1 andS e2) rewrite (PostTrueHelper e1) | (PostTrueHelper e2) = refl

    PostTrue : ∀ (s : Stmt) (c : Cnd) → HoareTriple (c) s (cndBool true)
    PostTrue = λ s c → HTSymbolicEnvProof (ConditionHoldsProof (PostTrueHelper (SymbolicExec zero (StatesSatisfying c) s)))
