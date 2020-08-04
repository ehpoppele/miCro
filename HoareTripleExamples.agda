module HoareTripleExamples where

    open import Language.miCro
    open import Language.miCro_parser
    open import Language.miCro_tokenizer
    open import Semantics.Expressions
    open import Semantics.Conditions
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl; cong; sym)
    open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
    open import Agda.Builtin.Bool
    open import HoareTriples

    --Needed for some proofs; not in agda standard library?
    cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
      → u ≡ x
      → v ≡ y
      -------------
      → f u v ≡ f x y
    cong₂ f refl refl  =  refl
    ----------

    PreFalseEx1 : SEnvSatisfiesCnd falseS (cndBool true) ≡ true
    PreFalseEx1 = refl

    PreFalseExample : HoareTriple (cndBool false) No-op (cndBool true)
    PreFalseExample = HTSymbolicEnvProof (ConditionHoldsProof PreFalseEx1) 

    PreFalseHelper : ∀ (s : Stmt) (n : Nat) → (SymbolicExec n falseS s) ≡ falseS
    PreFalseHelper (AssignVar str e) n = refl
    PreFalseHelper (IfElse c s1 s2) n rewrite (PreFalseHelper s2 n) = refl
    PreFalseHelper (Seq s1 s2) n rewrite (PreFalseHelper s1 n) rewrite (PreFalseHelper s2 (suc n)) = refl
    --These ones will need to be update once while/heap ops are added/changed
    PreFalseHelper (While zero c s) n = refl
    PreFalseHelper (While (suc n2) c s) n = refl
    PreFalseHelper (ReadHeap var e) n = refl
    PreFalseHelper (WriteHeap e1 e2) n = refl
    PreFalseHelper (New var e) n = refl
    PreFalseHelper No-op n = refl

    PreFalseHelper2 : ∀ (s : Stmt) (c : Cnd) → SEnvSatisfiesCnd (SymbolicExec 1 falseS s) c ≡ true
    PreFalseHelper2 s c = 
      begin
        SEnvSatisfiesCnd (SymbolicExec 1 falseS s) c
      ≡⟨ cong₂ (SEnvSatisfiesCnd) (PreFalseHelper s 1) refl ⟩
        SEnvSatisfiesCnd falseS c
      ≡⟨⟩
        true
      ∎
      
    PreFalse : ∀ (s : Stmt) (c : Cnd) → HoareTriple (cndBool false) s (c)
    PreFalse s c = HTSymbolicEnvProof (ConditionHoldsProof (PreFalseHelper2 s (CFCnd c)))

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
    PostTrue = λ s c → HTSymbolicEnvProof (ConditionHoldsProof (PostTrueHelper (SymbolicExec 1 (StatesSatisfying (CFCnd c)) s)))

    -- Hoare Triple Testing with concrete examples

    AssignXBasic : HoareTriple (cndBool true) (parseString "x = 1;") ((readVar "x") == const 1)
    AssignXBasic = HTSymbolicEnvProof (ConditionHoldsProof refl)

    BasicTest : SymbolicExec 1 trueS (parseString "x = x + 1;") ≡ (times (readVar "x") 1) ==S (plus (readVar "x1") (const 1))
    BasicTest = refl

    BasicTest2 :  ReplaceInCnd 1 "x" (plus (readVar "x1") (const 1)) (times (readVar "x") 1 > const 0) ≡ (times (plus (readVar "x1") (const 1)) 1 > const 0)
    BasicTest2 = refl

    BasicTest3 : AlwaysTrue (times (plus (readVar "x1") (const 1)) 1 > const 0) ≡ true
    BasicTest3 =
      begin
        AlwaysTrue (times (plus (readVar "x1") (const 1)) 1 > const 0)
      ≡⟨⟩
        ExpLessThan (const 0) (plus (times (readVar "x1") 1) (const 1))
      ≡⟨⟩
        true
      ∎

    IncXBasic : HoareTriple (cndBool true) (parseString "x = x + 1;") (readVar "x" > const 0)
    IncXBasic = HTSymbolicEnvProof (ConditionHoldsProof refl)

    BasicTest4 : SymbolicExec 1 trueS (parseString "x = y + 1;") ≡ ((times (readVar "x") 1) ==S (plus (readVar "y") (const 1)))
    BasicTest4 = refl

    BasicTest5 : ModifyCnd (((times (readVar "x") 1) ==S (plus (readVar "y") (const 1)))) (readVar "x" > readVar "y") ≡ (plus (readVar "y") (const 1)) > times (readVar "y") 1
    BasicTest5 = refl

    BasicTest6 : ExpLessThan (times (readVar "y") 1) (plus (times (readVar "y") 1) (const 1)) ≡ true
    BasicTest6 = refl

    IncXY : [ cndBool true ] (parseString "x = y + 1;") [ readVar "x" > readVar "y" ]
    IncXY = HTSymbolicEnvProof (ConditionHoldsProof refl)

    
