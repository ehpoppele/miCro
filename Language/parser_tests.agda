--- Unit Tests for Parser Functions ---
-- Some have been removed since they use functions removed from the parser or from the language
-- Most tests are functional and confirm that the parser behaves as expected

module Language.parser_tests where
    open import Language.miCro
    open import Language.miCro_parser
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl) -- For test programs
    open import Agda.Builtin.Bool

    -- First set of tests, for Token Operation Functions

    -- Tokens 1 should be "((+)==)<(>)-3+4"
    tokens1 = "(" :t: "(" :t: "+" :t: ")" :t: "==" :t: ")" :t: "<" :t: "(" :t: ">" :t: ")" :t: "-" :t: "3" :t: "+" :t: "4" :t: [t]

    {- unused
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
    -}

    natStr1 = "45"
    natStr2 = "2"
    natStr3 = "0"
    nonNatStr = "-9"

    natTest1 : (stringToNat natStr1) ≡ 45
    natTest1 = refl

    natTest2 : (stringToNat natStr2) ≡ 2
    natTest2 = refl

    natTest3 : (stringToNat natStr3) ≡ 0
    natTest3 = refl

    natTest4 : (isNumber (primStringToList natStr3)) ≡ true
    natTest4 = refl

    natTest5 : (isNumber (primStringToList nonNatStr)) ≡ false
    natTest5 = refl

    -- Second set of tests, for parsing expressions and conditions

    -- Tokens 2 is "5 + [x * 4]"
    tokens2 = "5" :t: "+" :t: "[" :t: "x" :t: "*" :t: "4" :t: "]" :t: [t]

    parseTest1 : (parseExp tokens2) ≡ Some([t] × (plus (const 5) (times (readVar "x") 4)))
    parseTest1 = refl

    -- Tokens 3 is "4 - 5 + 4"
    tokens3 = "3" :t: "-" :t: "2" :t: "+" :t: "1" :t: [t]

    parseTest2 : (parseExp tokens3) ≡ Some([t] × (plus (minus (const 3) (const 2)) (const 1)))
    parseTest2 = refl

    -- Tokens 4 is "[x * 4] - 5 + [4 - y]"
    tokens4 = "[" :t: "x" :t: "*" :t: "4" :t: "]" :t: "-" :t: "5" :t: "+" :t: "[" :t: "4" :t: "-" :t: "y" :t: "]" :t: [t]

    parseTest3 : (parseExp tokens4) ≡ Some([t] × (plus (minus (times (readVar "x") 4) (const 5)) (minus (const 4) (readVar "y"))))
    parseTest3 = refl

    -- parseTest4 below was having troubles with the new parser, so I wrote this series of tests to break it down and catch the various errors as I went
    -- One of the biggest issues currently is a failure to parse simply returns None with no useful information
    parseTestExpComp1 : (parseExp ("x" :t: "<" :t: [t])) ≡ Some(("<" :t: [t]) × (readVar "x"))
    parseTestExpComp1 = refl

    parseTestExpComp2 : (parseCnd ("true" :t: "or" :t: "x" :t: "<" :t: "3" :t: [t])) ≡ Some([t] × ((cndBool true) Or ((readVar "x") < (const 3))))
    parseTestExpComp2 = refl

    parseTestExpComp3 : (parseCnd ("(" :t: "not" :t: "true" :t: ")" :t:  "or" :t: "x" :t: "<" :t: "3"  :t: [t])) ≡ Some([t] × ((Not (cndBool true)) Or ((readVar "x") < (const 3))))
    parseTestExpComp3 = refl

    -- Tokens 5 is "(not true) or x < 3 and false or x >= 5"
    tokens5 = "(" :t: "not" :t: "true" :t: ")" :t:  "or" :t: "x" :t: "<" :t: "3" :t: "and" :t: "false" :t: "or" :t: "x" :t: ">=" :t: "5" :t: [t]

    parseTest4 : (parseCnd tokens5) ≡ Some([t] × (((Not (cndBool true)) Or (((readVar "x") < (const 3)) And (cndBool false))) Or ((readVar "x") >= (const 5))))
    parseTest4 = refl

    -- Higher-level parse tests, for statements and environments

    -- Tokens 6 is x = 1; x = x + 1;
    tokens6 = "x" :t: "=" :t: "1" :t: ";" :t: "x" :t: "=" :t: "x" :t: "+" :t: "1" :t: [t]

    parseTest5 : (parseTokens tokens6) ≡ (Seq (AssignVar "x" (const 1)) (AssignVar "x" (plus (readVar "x") (const 1))) )
    parseTest5 = refl

    -- Tokens 7 is "(x = 2, y = 3)"
    tokens7 = "(" :t: "x" :t: "=" :t: "2" :t: "," :t: "y" :t: "=" :t: "3" :t: ")" :t: [t]

    {- tests relating to parsing INIT, env, and removed features
    parseTest6 : (parseEnv tokens7) ≡ (Var Natural "x" 2) :e: (Var Natural "y" 3) :e: [e]
    parseTest6 = refl

    -- Tokens 8 is "INIT (x=2, y=3); x = x + 1;"
    tokens8 = "INIT" :t: "(" :t: "x" :t: "=" :t: "2" :t: "," :t: "y" :t: "=" :t: "3" :t: ")" :t: ";" :t: "x" :t: "=" :t: "x" :t: "+" :t: "1" :t: ";" :t: [t]

    runTest : (run tokens8) ≡ ((Var Natural "x" 3) :e: (Var Natural "y" 3) :e: [e]) & [h]
    runTest = refl
    -}

    -- Tokens 9 is "while (y < 9) {x = x + y; y = y + 2;}"
    tokens9 = "while" :t: "(" :t: "y" :t: "<" :t: "9" :t: ")" :t: "{" :t: "x" :t: "=" :t: "x" :t: "+" :t: "y" :t: ";" :t: "y" :t: "=" :t: "y" :t: "+" :t: "2" :t: ";" :t: "}" :t: [t]

    parseTest7 : (parseTokens tokens9) ≡ (While 512 ((readVar "y") < (const 9)) (Seq (AssignVar "x" (plus (readVar "x") (readVar "y"))) (AssignVar "y" (plus (readVar "y") (const 2))) ))
    parseTest7 = refl

    -- tokens 10 is "if (x < 10) {while (x > 7) {x = x - 1;}}"
    tokens10 = "if" :t: "(" :t: "x" :t: "<" :t: "10" :t: ")" :t: "{" :t: "while" :t: "(" :t: "x" :t: ">" :t: "7" :t: ")" :t: "{" :t: "x" :t: "=" :t: "x" :t: "-" :t: "1" :t: ";" :t: "}" :t: "}" :t: [t]

    bracketsTest1 : (parseTokens tokens10) ≡ IfElse ((readVar "x") < (const 10)) (While 512 ((readVar "x") > (const 7)) (AssignVar "x" (minus (readVar "x") (const 1)))) (No-op)
    bracketsTest1 = refl

    -- Tokens 11 is "y = &[1 + 2]"
    tokens11 = "y" :t: "=" :t: "&" :t: "[" :t: "1" :t: "+" :t: "2" :t: "]" :t: [t]
    
    --heapTest2 : (parseTokens tokens11) ≡ (AssignVar Natural "y" (readAddress (plus (const 1) (const 2))))
    --heapTest2 = refl

    -- Tokens 12 is "&[1] = 5;"
    --tokens12 = "&" :t: "[" :t: "1" :t: "]" :t: "=" :t: "5" :t: ";" :t: [t]

    --heapTest3 : (parseTokens tokens12) ≡ (WriteHeap (const 1) (const 5))
    --heapTest3 = refl
