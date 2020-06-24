open import miCro
open import miCro_parser
open import miCro_tokenizer
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl) -- For test programs
open import Agda.Builtin.Bool

prog1 = "
INIT;
ptr x = 3;
ptr y = 4;
[1] = 5;
z = x + y;
z = z + [x] + [y];
"

ptrTest1 : (run (tokenize prog1)) ≡ ((Var Pointer "x" 0) :e: (Var Pointer "y" 1) :e: (Var Natural "z" 9) :e: [e]) & (3 :H: 5 :H: [h])
ptrTest1 = refl

prog2 = "
INIT;
ptr x = 4;
ptr y = 2;
ptr z = 1;
ptr w = 3;
ptr last = 5;
curr = 8;
if (curr < 1) {
  while ([curr] > [curr + 1]) {
    vanishingVariable = [curr];
    [curr] = [curr + 1];
    [curr + 1] = vanishingVariable;
    curr = curr + 1;
  };
};
"

ptrTest2 : (run (tokenize prog2)) ≡ ((Var Pointer "x" 0) :e: (Var Pointer "y" 1) :e: (Var Pointer "z" 2) :e: (Var Pointer "w" 3) :e: (Var Pointer "last" 4) :e: (Var Natural "curr" 8) :e: [e]) & (404 :H: 0 :H: 1 :H: 3 :H: 5 :H: [h])
ptrTest2 = refl
  
