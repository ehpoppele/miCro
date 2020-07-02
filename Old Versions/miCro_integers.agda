-- Code for basic C-style language in agda --

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl) -- For test programs


module miCro where

  --- --- Basic Components; not used directly when writing miCro code --- ---
  
  -- Orders, Used for compare function --
  data Order : Set where
    Less : Order
    Equal : Order
    Greater : Order

  -- Natural Numbers, for Integer Use and to allow use of digits --
  data Nat : Set where
    zero : Nat
    suc  : Nat → Nat
  {-# BUILTIN NATURAL Nat #-}

  _ℕ+_ : Nat → Nat → Nat
  zero  ℕ+ m = m
  suc n ℕ+ m = suc (n ℕ+ m)
  {-# BUILTIN NATPLUS _ℕ+_ #-}

  -- Integers and Arithmetic, for Expressions. Things get very messy since we have to make cases for pos zero and neg zero --
  -- I can't find a good way to fix this; we need zero as a nat if we want to use "0"; could just make an int zero but then nat suc rules get in the way --
  -- Can't remember why I thought we needed ints; reverting to nats only will probably be much cleaner
  data Int : Set where
    pos    : Nat → Int
    neg : Nat → Int

  -- Comparison, between two integers. M and N here represent Nats. Messy cases because of pos, neg, and zero --
  compare : Int → Int → Order
  compare (pos zero) (pos zero) = Equal
  compare (neg zero) (neg zero) = Equal
  compare (pos zero) (neg zero) = Equal
  compare (neg zero) (pos zero) = Equal
  compare (pos (suc m)) (neg (suc n)) = Greater
  compare (neg (suc n)) (pos (suc m)) = Less
  compare (pos zero) (pos (suc m)) = Less
  compare (pos (suc m)) (pos zero) = Greater
  compare (neg zero) (pos (suc m)) = Less
  compare (pos (suc m)) (neg zero) = Greater
  compare (pos (suc m)) (pos (suc n)) = compare (pos m) (pos n)
  compare (pos zero) (neg (suc m)) = Greater
  compare (neg (suc m)) (pos zero) = Less
  compare (neg zero) (neg (suc m)) = Greater
  compare (neg (suc m)) (neg zero) = Less
  compare (neg (suc m)) (neg (suc n)) = compare (pos m) (pos n)

  
  -- Arithmetic for Integers. In these definitions, J is used for an integer, and N and M are used for nats that integers are built with --
  
  _+_ : Int → Int → Int
  pos zero + j = j
  neg zero + j = j
  j + pos zero = j --necessary since these aren't reflexively covered below, as in nat plus
  j + neg zero = j
  pos (suc n) + pos m = pos (suc (n ℕ+ m))
  neg (suc n) + neg m = neg (suc (n ℕ+ m))
  neg (suc n) + pos (suc m) = neg n + pos m
  pos (suc m) + neg (suc n) = pos m + neg n

  _-_ : Int → Int → Int
  j - (pos n) = (j + (neg n))
  j - (neg n) = (j + (pos n))

  {-# TERMINATING #-} -- I feel like this should be recognized as terminating, but last line throws it off I guess because addition is used (strange since addition is terminating(
  _*_ : Int → Int → Int
  j * (pos zero) = pos zero
  (pos zero) * j = pos zero
  j * (neg n) = (pos zero) - (j * (pos n))
  (neg n) * j = (pos zero) - (j * (pos n))
  j  * (pos (suc n)) = (j + (j  * (pos n)))

  --- --- Syntax part of miCro, these (along with integers) are used to actually write the code --- ---

  -- Expressions, for Assigning Variables --
  data Exp : Set where
    readX : Exp
    readX++ : Exp
    const : Int → Exp
    plus : Exp → Exp → Exp
    minus : Exp → Exp → Exp
    times : Exp → Exp → Exp

  -- Conditions --
  data Cnd : Set where
    True : Cnd
    False : Cnd
    _Or_ : Cnd → Cnd → Cnd
    _And_ : Cnd → Cnd → Cnd
    _==_ : Exp → Exp → Cnd
    _<_ : Exp → Exp → Cnd
    _>_ : Exp → Exp → Cnd
    _<=_ : Exp → Exp → Cnd
    _>=_ : Exp → Exp → Cnd
  
  -- Statements, making up the body of the code --
  data Stmt : Set where
    Seq : Stmt → Stmt → Stmt
    If : Cnd → Stmt → Stmt
    While : Cnd → Stmt → Stmt
    AssignX : Exp → Stmt

  --- --- Evaluation functions, including eval (applied to programs) and it's helper functions --- ---

  --Reduce Exp, to simplify Exp to const values --
  {-# TERMINATING #-} --Will terminate, but agda doesn't recognize that (must either result in a const or progress through a chain of arithmetic)
  reduceExp : Exp → Int → Exp
  reduceExp (readX) x = const x
  reduceExp (readX++) (pos m) = const (pos (suc m))
  reduceExp (readX++) (neg (suc m)) = const (neg m)
  reduceExp (readX++) (neg zero) = const (pos (suc zero))
  reduceExp (const n) x = const n
  reduceExp (plus (const m) (const n)) x = const (m + n)
  reduceExp (plus e1 e2) x = reduceExp (plus (reduceExp e1 x)  (reduceExp e2 x)) x
  reduceExp (minus (const m) (const n)) x = const (m - n) 
  reduceExp (minus e1 e2) x = reduceExp(minus (reduceExp e1 x) (reduceExp e2 x)) x
  reduceExp (times (const m) (const n)) x = const (m * n)
  reduceExp (times e1 e2) x = reduceExp(times (reduceExp e1 x) (reduceExp e2 x)) x

  -- Reduce, to simplify Cnd to boolean values --
  {-# TERMINATING #-} --Actually must terminate, but agda again can't tell (since here we also use reduceExp)
  reduceCnd : Cnd → Int → Cnd
  reduceCnd True _ = True
  reduceCnd False _ = False
  reduceCnd (False And c2) _ = False
  reduceCnd (True And False) _ = False
  reduceCnd (True And True) _ = True
  reduceCnd (c1 And c2) x = reduceCnd ((reduceCnd c1 x) And (reduceCnd c2 x)) x
  reduceCnd (True Or c2) _ = True
  reduceCnd (False Or True) _ = True
  reduceCnd (False Or False) _ = False
  reduceCnd (c1 Or c2) x = reduceCnd ((reduceCnd c1 x) Or (reduceCnd c2 x)) x
  reduceCnd (const j == const k) _ with compare j k
  ... | Less = False
  ... | Equal = True
  ... | Greater = False
  reduceCnd (e1 == e2) x = reduceCnd ((reduceExp e1 x) ==(reduceExp e2 x)) x
  reduceCnd (const j < const k) _ with compare j k
  ... | Less = True
  ... | Equal = False
  ... | Greater = False
  reduceCnd (e1 < e2) x = reduceCnd ((reduceExp e1 x) < (reduceExp e2 x)) x
  reduceCnd (const j > const k) _ with compare j k
  ... | Less = False
  ... | Equal = False
  ... | Greater = True
  reduceCnd (e1 > e2) x = reduceCnd ((reduceExp e1 x) > (reduceExp e2 x)) x
  reduceCnd (e1 <= e2) x = reduceCnd ((e1 < e2) Or (e1 == e2)) x
  reduceCnd (e1 >= e2) x = reduceCnd ((e1 > e2) Or (e1 == e2)) x

  -- Const Exp to Natural number function --
  constToInt : Exp → Int
  constToInt (const n) = n
  constToInt e = (pos 0) --just to fill pattern; shouldn't be calling this on non-const Exps

  -- Evaluation function, taking value of variable and code for input, producing value of variable at the end --
  {-# TERMINATING #-} --Not actually guaranteed to terminate, because of while; need to be careful writing programs or it will basically freeze my computer
  eval : Stmt → Int → Int
  eval (Seq s1 s2) x = eval s2 (eval s1 x)
  eval (If False s) x = x
  eval (If True s) x = eval s x
  eval (If c s) x = eval (If (reduceCnd c x) s) x
  eval (While False s) x = x
  eval (While c s) x = eval (If c (Seq s (While c s))) x
  eval (AssignX e) x = constToInt (reduceExp e x)


  --- --- Test Programs --- ---
  -- Everything has to be written on one line I think since agda pays attention to white space --
  -- form is eval (code) (init x) ≡ expected outcome --
  -- Everything is nicely reflexive; intrinsic proofs I guess based on the typing? --
  
  test1 : ∀ ( n : Int ) → eval (Seq (AssignX (const (pos 1))) (AssignX readX++)) n ≡ pos 2
  test1 n = refl

  test2 : eval (If (readX == (const (pos 0))) (AssignX (plus readX (const (pos 1))))) (pos 0) ≡ pos 1
  test2 = refl

  test3 : eval (While (readX == (const (pos 0))) (AssignX (plus readX (const (pos 1))))) (pos 0) ≡ pos 1
  test3 = refl

  whileTest : eval (While (readX < (const (pos 10))) (AssignX readX++)) (pos 0) ≡ (pos 10)
  whileTest = refl 

  -- Can't do much without multiple vars, but this repeatedly X as long as it is less than or equal to 32 --
  greatestLesserPower : eval (While (readX <= (const (pos 32))) (AssignX (times readX readX))) (pos 2) ≡ pos 256
  greatestLesserPower = refl


  --- Further work: Replace single-variable X with arbitrary-size variable set (env) ---
 -- Review lists, pairs, tuples etc to clean this up
 -- Goal is similar to: Vars = (v1, (v2, (v3, None)))
 -- with v1 = ("X", Bool, False), v2 = ("Y", Int, (pos 0)), v3 = ("Z", Int, (neg 9)) 
 -- VariableSet : Set
 --  None : VariableSet
 --  _&_ : Var → VariableSet → VariableSet
 -- Var : String → VarData
 -- data VarData : Set where
 --   BoolVar : Bool → VarData
 --   IntVar : Int → VarData
