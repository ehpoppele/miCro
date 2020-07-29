module HoareTripleExamples where

    open import Language.miCro
    open import Language.miCro_parser
    open import Semantics.Expressions
    open import Semantics.Conditions
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl)
    open import Agda.Builtin.Bool
    open import HoareTriples

    PreFalse1 : SEnvSatisfiesCnd falseS (cndBool true) ≡ true
    PreFalse1 = refl

    PreFalse : HoareTriple (cndBool false) No-op (cndBool true)
    PreFalse = HTSymbolicEnvProof (ConditionHoldsProof PreFalse1)
