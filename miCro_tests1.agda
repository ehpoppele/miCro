open import Interpreter.miCro_tokenizer
open import Interpreter.miCro_parser
open import Interpreter.miCro
open import Agda.Builtin.Bool
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl) -- For test programs
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (+-assoc)

sum = "
      while (x < 10) {
        x = x + 1;
        y = y + x;
       };
       "

microTest1 : (run (tokenize sum)) ≡ ((Var Natural "x" 10) :e: (Var Natural "y" 55) :e: [e]) & _
microTest1 = refl

greatestLesserSquare = "
input = 65;
square = 0;
i = 0;
while ([i * i] < input) {
  square = i * i;
  i = i + 1;
  }
"

microTest2 : (run (tokenize greatestLesserSquare)) ≡ ((Var Natural "input" 65) :e: (Var Natural "square" 64) :e: (Var Natural "i" 9) :e: [e]) & _
microTest2 = refl

-- Program should be run with input = [value] in the initial environment
sumSquare = "
sum = 0;
while (input > 0) {
  input = input - 1;
  sum = sum + [2 * input] + 1;
}
"

addTwice = "
x = x + 1;
x = x + 1;
"

addTwo = "
x = x +2;
"

plusTwoTest : ∀ ( n : Nat ) → ((exec (((Var Natural "x" n) :e: [e]) & [h]) (parseTokens (tokenize addTwice))) ≡  (exec (((Var Natural "x" n) :e: [e]) & [h]) (parseTokens (tokenize addTwo))))
plusTwoTest n =
  begin
  (Var Natural "x" ((n + stringToNat "1") + stringToNat "1") :e: [e]) & [h]
  ≡⟨⟩
  (Var Natural "x" ((n + stringToNat "1") + 1) :e: [e]) & [h]
  ≡⟨⟩
  (Var Natural "x" ((n + 1) + 1) :e: [e]) & [h]
  ≡⟨ +-assoc n 1 1 ⟩
  (Var Natural "x" (n + (1 + 1)) :e: [e]) & [h]
  ∎
  

{-
squareTest1 : (exec (((Var Natural "input" 8) :e: [e]) & [h]) (parseTokens (tokenize sumSquare))) ≡ ((Var Natural "input" 0) :e: (Var Natural "sum" 64) :e: [e]) & _
squareTest1 = refl

timesSquare = "
sum = input * input;
"

squareTest2 : ∀ ( n : Nat) → (exec (((Var Natural "input" n) :e: [e]) & [h]) (parseTokens (tokenize sumSquare))) ≡ (exec (((Var Natural "input" n) :e: [e]) & [h]) (parseTokens (tokenize timesSquare)))
squareTest2 zero = refl
squareTest2 (suc n) rewrite = ?
-}
