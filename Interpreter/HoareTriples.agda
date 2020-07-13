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
  
  
