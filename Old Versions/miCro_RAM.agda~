-- Code for basic C-style language in agda --

module miCro where

  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl) -- For test programs

  --- --- Basic Components; not used directly when writing miCro code --- ---

  postulate String : Set
  {-# BUILTIN STRING String #-}

  -- Agda builtin Booleans. These are "true" and "false" and are required within the syntax; the chck function will reduce a cnd to one of these booleans.
  open import Agda.Builtin.Bool

  -- Added Bool functions
  boolAnd : Bool → Bool → Bool
  boolAnd true true = true
  boolAnd c1 c2 = false

  boolOr : Bool → Bool → Bool
  boolOr true c2 = true
  boolOr c1 true = true
  boolOr c1 c2 = false

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
    [e]  : Env
    _:e:_ : Variable → Env → Env

  infixr 5 _:e:_

  -- Expressions, for Assigning Variables --
  data Exp : Set where
    readVar : String → Exp
    readVar++ : String → Exp
    plus : Exp → Exp → Exp
    const : Nat → Exp
    minus : Exp → Exp → Exp
    times : Exp → Exp → Exp

  -- Conditions --
  data Cnd : Set where
    cndBool : Bool → Cnd
    Not : Cnd → Cnd
    _Or_ : Cnd → Cnd → Cnd
    _And_ : Cnd → Cnd → Cnd
    _==_ : Exp → Exp → Cnd
    _!=_ : Exp → Exp → Cnd
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
    No-op : Stmt

  --- --- Evaluation functions, including eval (applied to programs) and it's helper functions --- ---

  --Reduce Exp, to simplify Exp to const values --
  eval : Env → Exp → Nat
  eval [e] (readVar str)  = zero -- If we can't find the variable we're trying to read, just return zero
  eval ((Var str2 x) :e: v) (readVar str1)with primStringEquality str1 str2
  ...                                             | true = x
  ...                                             | false = eval v (readVar str1)
  eval [e] (readVar++ str) = 1 --I don't know if this makes any sense; perhaps still return zero since var can't be found?
  eval ((Var str2 x) :e: v) (readVar++ str1) with primStringEquality str1 str2
  ...                                             | true = suc x
  ...                                             | false = eval v (readVar++ str1)
  eval v (const n) = n
  eval v (plus e1 e2) = (eval v e1) + (eval v e2)
  eval v (minus e1 e2) = (eval v e1) - (eval v e2)
  eval v (times e1 e2) = (eval v e1) * (eval v e2)

  -- Reduce, to simplify Cnd to boolean values --
  check : Env → Cnd → Bool
  check v (Not c) with check v c
  ... | false = true
  ... | true = false
  check _ (cndBool b) = b
  check v (c1 And c2)  = boolAnd (check v c1) (check v c2)
  check v (c1 Or c2)  = boolOr (check v c1) (check v c2)
  check v (j == k)  with compare (eval v j) (eval v k)
  ... | Less = false
  ... | Equal = true
  ... | Greater = false
  check v (j != k) with compare (eval v j) (eval v k)
  ... | Less = true
  ... | Equal = false
  ... | Greater = true
  check v (j < k)  with compare (eval v j) (eval v k)
  ... | Less = true
  ... | Equal = false
  ... | Greater = false
  check v (j > k)  with compare (eval v j) (eval v k)
  ... | Less = false
  ... | Equal = false
  ... | Greater = true
  check v (j <= k) with compare (eval v j) (eval v k)
  ... | Less = true
  ... | Equal = true
  ... | Greater = false
  check v (j >= k) with compare (eval v j) (eval v k)
  ... | Less = false
  ... | Equal = true
  ... | Greater = true

  -- Update function, to write variables in environment --
  update : Env → String → Nat → Env
  update [e] str x = ((Var str x) :e: [e])
  update ((Var str1 n) :e: v) str2 x with primStringEquality str1 str2
  ... | true = ((Var str1 x) :e: v)
  ... | false = ((Var str1 n) :e: (update v str2 x))

  -- Evaluation function, taking value of variable and code for input, producing value of variable at the end --
  {-# TERMINATING #-} --Not actually guaranteed to terminate, because of while; need to be careful writing programs or it will basically freeze my computer
  exec : Env → Stmt → Env
  exec v (Seq s1 s2) = exec (exec v s1) s2
  exec v (If c s) with (check v c)
  ...                 | true = exec v s
  ...                 | false = v
  exec v (IfElse c s1 s2) with (check v c)
  ...                         | true = exec v s1
  ...                         | false = exec v s2
  exec v (While c s) with (check v c)
  ... | false = v
  ... | true = exec v (Seq s (While c s))
  exec v (AssignVar str e) = update v str (eval v e)
  exec v No-op = v

  --- --- Test Programs --- ---
  -- Everything has to be written on one line I think since agda pays attention to white space --
  -- form is exec (code) (init x) ≡ expected outcome --
  -- Everything is nicely reflexive; intrinsic proofs I guess based on the typing? --
  
  test1 : ∀ ( n : Nat ) → exec  ((Var "X" n) :e: [e]) (Seq (AssignVar "X" (const 1)) (AssignVar "X" (readVar++ "X"))) ≡ ((Var "X" 2) :e: [e])
  test1 n = refl

  test2 : exec [e] (If ((readVar "X") == (const 0)) (AssignVar "X" (plus (readVar "X") (const 1)))) ≡ ((Var "X" 1) :e: [e])
  test2 = refl

  test3 : exec [e] (While ((readVar "X") == (const 0)) (AssignVar "X" (plus (readVar "X") (const 1)))) ≡ ((Var "X" 1) :e: [e])
  test3 = refl


  whileTest : exec [e] (While ((readVar "X") < (const 10)) (AssignVar "X" (plus (const 1) (readVar "X")))) ≡ ((Var "X" 10) :e: [e])
  whileTest = refl 

  -- Can't do much without multiple vars, but this repeatedly X as long as it is less than or equal to 32 --
  greatestLesserPower : exec ((Var "X" 2) :e: [e]) (While ((readVar "X") <= (const 32)) (AssignVar "X" (times (readVar "X") (readVar "X")))) ≡ ((Var "X" 256) :e: [e])
  greatestLesserPower = refl

  -- Test with multiple Variables, based on Hoare Logic pdf from UW --

  UWEx1 : exec [e] (While ((readVar "k") <= (const 4)) (Seq (AssignVar "sum" (plus (readVar "k") (readVar "sum"))) (AssignVar "k" (readVar++ "k")))) ≡ ((Var "sum" 10) :e: (Var "k" 5) :e: [e])
  UWEx1 = refl

-- To Add: Rules on equivalence of Env; if Env A contains Env B, then A ≡ B? or some similar relation, so that rhs of above statement/proofs can be condensed to only 1 variable --

