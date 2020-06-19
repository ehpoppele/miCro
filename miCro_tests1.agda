open import miCro_tokenizer
open import miCro_parser
open import miCro
open import Agda.Builtin.Bool
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl) -- For test programs

sum = "INIT (x = 0);
      while (x < 10) {
        x = x + 1;
        y = y + x;
       };"

microTest1 : (run (tokenize sum)) ≡ ((Var "x" 10) :e: (Var "y" 55) :e: [e])
microTest1 = refl

greatestLesserSquare = "

INIT (input = 65);

while ((i * i) < input) {
  square = i * i;
  i = i + 1;
  }
"

microTest2 : (run (tokenize greatestLesserSquare)) ≡ (Var "input" 65) :e: (Var "square" 64) :e: (Var "i" 9) :e: [e]
microTest2 = refl
