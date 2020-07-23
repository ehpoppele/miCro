module Interpreter.HoareTriples where

  open import Interpreter.miCro
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open import Agda.Builtin.Bool

  data evalsTo : Env → Exp → Nat → Set where
    evalsTrue : ∀ {env : Env} {x : Exp} {n : Nat}
      → (eval (env & [h]) x) ≡ n
      ------------
      → evalsTo env x n

  basicEval : evalsTo [e] (readVar "x") zero
  basicEval = evalsTrue refl

  --Change checks to to checks true?
  data checksTo : Env → Cnd → Bool → Set where
    checksOut : ∀ {env : Env} {c : Cnd} {b : Bool}
      → (check (env & [h]) c) ≡ b
      -------------------
      → checksTo env c b

  basicCheck : checksTo [e] ((readVar "x") <= (const 1)) true
  basicCheck = checksOut refl

  data execsTo : Env → Stmt → Env → Set where
    execsCorrect : ∀ {e1 e2 : Env} {s : Stmt}
      → (exec (e1 & [h]) s) ≡ (e2 & [h])
      ----------------------------
      → execsTo e1 s e2

  basicExec : execsTo [e] (If ((readVar "X") == (const 0)) (AssignVar "X" (plus (readVar "X") (const 1)))) ((Var "X" 1) :e: [e])
  basicExec = execsCorrect refl

---------------------------------------

  --I think this doesn't yet work for {false} s {anything}
  data HoareTriple : Cnd → Stmt → Cnd → Set where
    HoareTripleGeneral : ∀ {e1 e2 : Env} {c1 c2 : Cnd} {s : Stmt}
      → (execsTo e1 s e2)
      → (checksTo e1 c1 true)
      → (checksTo e2 c2 true)
      ------------------------
      → HoareTriple c1 s c2

{-
  data HoareTriple : Cnd → Stmt → Cnd → Set where
    HoareTripleTrue : ∀
      → --evidence of some Env st. 
  

  HoareAlwaysTrue : ∀ (s : Stmt) (c1 c2 : Cnd)
    → (∀ {e2 : Env} → (checksTo e2 c2 true))
    ---------------------
    → HoareTriple c1 s c2
  HoareAlwaysTrue s c1 c2 x = HoareTripleTrue {!e1!} {!!} {!!} {!!} {!!} -}
