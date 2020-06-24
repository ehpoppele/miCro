--- Unit Tests for Parser Functions ---

open import miCro
open import miCro_parser
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl) -- For test programs
open import Agda.Builtin.Bool

-- First set of tests, for Token Operation Functions

-- Tokens 1 should be "((+)==)<(>)-3+4"
tokens1 = "(" :t: "(" :t: "+" :t: ")" :t: "==" :t: ")" :t: "<" :t: "(" :t: ">" :t: ")" :t: "-" :t: "3" :t: "+" :t: "4" :t: [t]

tokensTest1 : (splitL tokens1 "<") ≡ ("(" :t: "(" :t: "+" :t: ")" :t: "==" :t: ")" :t: [t])
tokensTest1 = refl

tokensTest2 : (splitR tokens1 "+") ≡ "4" :t: [t]
tokensTest2 = refl

tokensTest3 : (token_search tokens1 "-")≡ true
tokensTest3 = refl

tokensTest4 : (token_search tokens1 ">") ≡ false
tokensTest4 = refl

tokensTest5 : (comp_token_search tokens1) ≡ "<"
tokensTest5 = refl

tokensTest6 : (pm_search tokens1) ≡ "-"
tokensTest6 = refl

natStr1 = "45"
natStr2 = "2"
natStr3 = "0"
nonNatStr = "-9"

natTest1 : (string_to_nat natStr1) ≡ 45
natTest1 = refl

natTest2 : (string_to_nat natStr2) ≡ 2
natTest2 = refl

natTest3 : (string_to_nat natStr3) ≡ 0
natTest3 = refl

natTest4 : (is_number (primStringToList natStr3)) ≡ true
natTest4 = refl

natTest5 : (is_number (primStringToList nonNatStr)) ≡ false
natTest5 = refl

-- Second set of tests, for parsing expressions and conditions

-- Tokens 2 is "5 + (4 * x)"
tokens2 = "5" :t: "+" :t: "(" :t: "4" :t: "*" :t: "x" :t: ")" :t: [t]

parseTest1 : (parse_exp tokens2) ≡ (plus (const 5) (times (const 4) (readVar "x")))
parseTest1 = refl

-- Tokens 3 is "4 - 5 + 4"
tokens3 = "3" :t: "-" :t: "2" :t: "+" :t: "1" :t: [t]

parseTest2 : (parse_exp tokens3) ≡ (plus (minus (const 3) (const 2)) (const 1))
parseTest2 = refl

-- Tokens 4 is "(x * 4) - 5 + (4 - y)"
tokens4 = "(" :t: "x" :t: "*" :t: "4" :t: ")" :t: "-" :t: "5" :t: "+" :t: "(" :t: "4" :t: "-" :t: "y" :t: ")" :t: [t]

parseTest3 : (parse_exp tokens4) ≡ (plus (minus (times (readVar "x") (const 4)) (const 5)) (minus (const 4) (readVar "y")))
parseTest3 = refl

-- Tokens 5 is "(not true) or x < 3 and false or x >= 5"
tokens5 = "(" :t: "not" :t: "true" :t: ")" :t:  "or" :t: "x" :t: "<" :t: "3" :t: "and" :t: "false" :t: "or" :t: "x" :t: ">=" :t: "5" :t: [t]

parseTest4 : (parse_condition tokens5) ≡ (Not (cndBool true)) Or ((((readVar "x") < (const 3)) And (cndBool false)) Or ((readVar "x") >= (const 5)))
parseTest4 = refl

-- Higher-level parse tests, for statements and environments

-- Tokens 6 is x = 1; x = x + 1;
tokens6 = "x" :t: "=" :t: "1" :t: ";" :t: "x" :t: "=" :t: "x" :t: "+" :t: "1" :t: [t]

parseTest5 : (parse_stmt tokens6) ≡ (Seq (AssignVar Natural "x" (const 1)) (Seq (AssignVar Natural "x" (plus (readVar "x") (const 1))) No-op) )
parseTest5 = refl

-- Tokens 7 is "(x = 2, y = 3)"
tokens7 = "(" :t: "x" :t: "=" :t: "2" :t: "," :t: "y" :t: "=" :t: "3" :t: ")" :t: [t]

parseTest6 : (parse_env tokens7) ≡ (Var Natural "x" 2) :e: (Var Natural "y" 3) :e: [e]
parseTest6 = refl

-- Tokens 8 is "INIT (x=2, y=3); x = x + 1;"
tokens8 = "INIT" :t: "(" :t: "x" :t: "=" :t: "2" :t: "," :t: "y" :t: "=" :t: "3" :t: ")" :t: ";" :t: "x" :t: "=" :t: "x" :t: "+" :t: "1" :t: ";" :t: [t]

runTest : (run tokens8) ≡ ((Var Natural "x" 3) :e: (Var Natural "y" 3) :e: [e]) & [h]
runTest = refl

-- Tokens 9 is "while (y < 9) {x = x + y; y = y + 2;};"
tokens9 = "while" :t: "(" :t: "y" :t: "<" :t: "9" :t: ")" :t: "{" :t: "x" :t: "=" :t: "x" :t: "+" :t: "y" :t: ";" :t: "y" :t: "=" :t: "y" :t: "+" :t: "2" :t: ";" :t: "}" :t: ";" :t: [t]

parseTest7 : (parse_stmt tokens9) ≡ Seq (While ((readVar "y") < (const 9)) (Seq (AssignVar Natural "x" (plus (readVar "x") (readVar "y"))) (Seq (AssignVar Natural "y" (plus (readVar "y") (const 2))) (No-op)) )) No-op
parseTest7 = refl
