-- This file should not be loaded or run
-- Nearly all the syntax used for heap operations that appears here is outdated
-- Also it imports wrong

open import Interpreter.miCro
open import Interpreter.miCro_parser
open import Interpreter.miCro_tokenizer
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl) -- For test programs
open import Agda.Builtin.Bool

prog1 = "
* x = 3;
* y = 4;
&[1] = 5;
z = x + y;
z = z + &[x] + &[y];
"

ptrTest1 : (run (tokenize prog1)) ≡ ((Var Pointer "x" 0) :e: (Var Pointer "y" 1) :e: (Var Natural "z" 9) :e: [e]) & (3 :H: 5 :H: [h])
ptrTest1 = refl

prog2 = "
* x = 4;
* y = 2;
* z = 1;
* w = 3;
* last = 5;
curr = x;
if (&[curr + 0] == 4) {
  while (&[curr] > &[curr + 1]) {
    last = &[curr];
    &[curr] = &[curr + 1];
    &[curr + 1] = last;
    curr = curr + 1;
  };
};
"

ptrTest2 : (run (tokenize prog2)) ≡ ((Var Pointer "x" 0) :e: (Var Pointer "y" 1) :e: (Var Pointer "z" 2) :e: (Var Pointer "w" 3) :e: (Var Pointer "last" 4) :e: (Var Natural "curr" 3) :e: [e]) & (2 :H: 1 :H: 3 :H: 4 :H: 5 :H: [h])
ptrTest2 = refl

--Program 3 sums over a short linked list
prog3 = "
sum = 0;
* x = 5;
xNext = x + 1;
&[xNext] = 0;
* y = 3;
yNext = y + 1;
&[yNext] = 0;
* z = 2;
zNext = z + 1;
&[zNext] = 2011;
first = y;
&[yNext] = x;
&[xNext] = z;
curr = first;
while (&[curr+1] < 2011){
  sum = sum + &[curr];
  curr = &[curr + 1];
};
"

LLTest1 : (run (tokenize prog3)) ≡ (((Var Natural "sum" 8) :e: _)) & _
LLTest1 = refl


