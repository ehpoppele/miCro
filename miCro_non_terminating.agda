-- Code for basic C-style language in agda --
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl) -- For test programs


module miCro where

  --- --- Basic Components; not used directly when writing miCro code --- ---

  postulate String : Set
  {-# BUILTIN STRING String #-}

  -- Agda builtin Booleans. These are used only for string comparison primitives; the actual code uses True and False (caps on T and F) as a condition data type
  open import Agda.Builtin.Bool

  primitive
    primStringEquality : String → String → Bool

  -- Orders, Used for compare function --
  data Order : Set where
    Less : Order
    Equal : Order
    Greater : Order

  -- Natural Numbers, along with arithmetic and comparisons used for them. Replacing Ints since agda works better with nats  --
  data Nat : Set where
    zero : Nat
    suc  : Nat → Nat
  {-# BUILTIN NATURAL Nat #-}

  _+_ : Nat → Nat → Nat
  zero  + m = m
  suc n + m = suc (n + m)
  {-# BUILTIN NATPLUS _+_ #-}

  _-_ : Nat → Nat → Nat
  n     - zero  = n
  zero  - suc m = zero
  suc n - suc m = n - m
  {-# BUILTIN NATMINUS _-_ #-}

  _*_ : Nat → Nat → Nat
  zero  * m = zero
  suc n * m = (n * m) + m
  {-# BUILTIN NATTIMES _*_ #-}

  -- Comparison, between two natural numbers. M and N here represent Nats. Messy cases because of pos, neg, and zero --
  compare : Nat → Nat → Order
  compare zero zero = Equal
  compare zero (suc n) = Less
  compare (suc m) zero = Greater
  compare (suc m) (suc n) = compare m n

  --- --- Syntax part of miCro, these (along with integers) are used to actually write the code --- ---

  -- Variables, with two arguments for name and value, are combined in a variable list to use as environment --
  -- could also change later to BoolVar, IntVar, etc for more variable types
  data Variable : Set where
    Var : String → Nat → Variable

  data Env : Set where
    []  : Env
    _∷_ : Variable → Env → Env

  infixr 5 _∷_

  pattern [_] z = z ∷ []
  pattern [_,_] y z = y ∷ z ∷ []
  pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
  pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
  pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
  pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []
  

  -- Expressions, for Assigning Variables --
  data Exp : Set where
    readVar : String → Exp
    readVar++ : String → Exp
    const : Nat → Exp
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
    IfElse : Cnd → Stmt → Stmt → Stmt
    While : Cnd → Stmt → Stmt
    AssignVar : String → Exp → Stmt

  --- --- Evaluation functions, including eval (applied to programs) and it's helper functions --- ---

  --Reduce Exp, to simplify Exp to const values --
  {-# TERMINATING #-} --Will terminate, but agda doesn't recognize that (must either result in a const or progress through a chain of arithmetic)
  reduceExp : Exp → Env → Exp
  reduceExp (readVar str) []  = const zero -- If we can't find the variable we're trying to read, just return zero
  reduceExp (readVar str1) ((Var str2 x) ∷ v) with primStringEquality str1 str2
  ...                                             | true = const x
  ...                                             | false = reduceExp (readVar str1) v
  reduceExp (readVar++ str) []  = const 1
  reduceExp (readVar++ str1) ((Var str2 x) ∷ v) with primStringEquality str1 str2
  ...                                             | true = const (suc x)
  ...                                             | false = reduceExp (readVar str1) v
  reduceExp (const n) v = const n
  reduceExp (plus (const m) (const n)) v = const (m + n)
  reduceExp (plus e1 e2) v = reduceExp (plus (reduceExp e1 v)  (reduceExp e2 v)) v
  reduceExp (minus (const m) (const n)) v = const (m - n) 
  reduceExp (minus e1 e2) v = reduceExp(minus (reduceExp e1 v) (reduceExp e2 v)) v
  reduceExp (times (const m) (const n)) v = const (m * n)
  reduceExp (times e1 e2) v = reduceExp(times (reduceExp e1 v) (reduceExp e2 v)) v

  -- Reduce, to simplify Cnd to boolean values --
  {-# TERMINATING #-} --Actually must terminate, but agda again can't tell (since here we also use reduceExp)
  reduceCnd : Cnd → Env → Cnd
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
  constToNat : Exp → Nat
  constToNat (const n) = n
  constToNat e = 0 --just to fill pattern; shouldn't be calling this on non-const Exps

  -- Evaluation function, taking value of variable and code for input, producing value of variable at the end --
  {-# TERMINATING #-} --Not actually guaranteed to terminate, because of while; need to be careful writing programs or it will basically freeze my computer
  eval : Stmt → Env → Env
  eval (Seq s1 s2) v = eval s2 (eval s1 v)
  eval (If True s) v = eval s v
  eval (If False s) v = v
  eval (If c s) v = eval (If (reduceCnd c v) s) v
  eval (IfElse True s1 s2) v = eval s1 v
  eval (IfElse False s1 s2) v = eval s2 v
  eval (IfElse c s1 s2) v = eval (IfElse (reduceCnd c v) s1 s2) v
  eval (While False s) v = v
  eval (While c s) v = eval (If c (Seq s (While c s))) v
  eval (AssignVar str1 (const x)) [] = [(Var str1 x)]
  eval (AssignVar str1 (const x)) ((Var str2 n) ∷ v) with primStringEquality str1 str2
  ...  | true = ((Var str2 x) ∷ v)
  ...  | false = ((Var str2 n)∷(eval (AssignVar str1 (const x)) v))
  eval (AssignVar str1 e) v = eval (AssignVar str1 (reduceExp e v)) v


  --- --- Test Programs --- ---
  -- Everything has to be written on one line I think since agda pays attention to white space --
  -- form is eval (code) (init x) ≡ expected outcome --
  -- Everything is nicely reflexive; intrinsic proofs I guess based on the typing? --
  
  test1 : ∀ ( n : Nat ) → eval (Seq (AssignVar "X" (const 1)) (AssignVar "X" (readVar++ "X"))) [(Var "X" n)] ≡ [(Var "X" 2)]
  test1 n = refl

  test2 : eval (If ((readVar "X") == (const 0)) (AssignVar "X" (plus (readVar "X") (const 1)))) [(Var "X" 0)] ≡ [(Var "X" 1)]
  test2 = refl

  test3 : eval (While ((readVar "X") == (const 0)) (AssignVar "X" (plus (readVar "X") (const 1)))) [(Var "X" 0)] ≡ [(Var "X" 1)]
  test3 = refl

  whileTest : eval (While ((readVar "X") < (const 10)) (AssignVar "X" (plus (const 1) (readVar "X")))) []  ≡ [(Var "X" 10)]
  whileTest = refl 

  -- Can't do much without multiple vars, but this repeatedly X as long as it is less than or equal to 32 --
  greatestLesserPower : eval (While ((readVar "X") <= (const 32)) (AssignVar "X" (times (readVar "X") (readVar "X")))) [(Var "X" 2)] ≡ [(Var "X" 256)]
  greatestLesserPower = refl

  -- Test with multiple Variables, based on Hoare Logic pdf from UW --

  UWEx1 : eval (While ((readVar "k") <= (const 4)) (Seq (AssignVar "sum" (plus (readVar "k") (readVar "sum"))) (AssignVar "k" (readVar++ "k")))) [(Var "k" 0), (Var "sum" 0)] ≡ [(Var "k" 5), (Var "sum" 10)]
  UWEx1 = refl

  -- To Add: Rules on equivalence of Env; if Env A contains Env B, then A ≡ B? or some similar relation, so that rhs of above statement/proofs can be condensed to only 1 variable --
