module Interpreter.HoareTriplesMess where

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

  --I think this doesn't yet work for {false} s {anything}
  data HoareTriple : Cnd → Stmt → Cnd → Set where
    HoareTriplePrecise : ∀ {c1 c2 : Cnd} {s : Stmt}
      → (m : RAM)
      → (checksTo m c1 true)
      → (checksTo (exec m s) c2 true)
      ---------------------
      → HoareTriple c1 s c2
      {-
    HoareTripleGeneral : ∀ {e1 e2 : Env} {c1 c2 : Cnd} {s : Stmt}
      → (execsTo e1 s e2)
      → (checksTo e1 c1 true)
      → (checksTo e2 c2 true)
      ------------------------
      → HoareTriple c1 s c2
      -}

  basicTriple : HoareTriple ((readVar "x") == (const 3)) (AssignVar "x" (plus (readVar "x") (const 1))) ((readVar "x") == (const 4))
  basicTriple = HoareTriplePrecise (((Var "x" 3) :e: [e]) & [h]) (checksOut refl) (checksOut refl)

  HoareAlwaysTrue : ∀ (s : Stmt) (c1 c2 : Cnd)
    → (∀ {m2 : RAM} → (checksTo m2 c2 true))
    ---------------------
    → HoareTriple c1 s c2
  HoareAlwaysTrue s c1 c2 x = {!!}
