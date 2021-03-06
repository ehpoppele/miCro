-- Code for basic C-style language in agda --

module Language.miCro where

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

  boolIfElse : {A : Set} → Bool → A → A → A
  boolIfElse true a b = a
  boolIfElse false a b = b

  -- Orders, Used for compare functions on Nats (and in other files on strings) --
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

  primitive
    primStringEquality : String → String → Bool
    primStringAppend : String → String → String
    primShowNat : Nat → String

  -- Nat comparisons, for when a bool rather than an order is needed
  NatEquality : Nat → Nat → Bool
  NatEquality zero zero = true
  NatEquality zero (suc n) = false
  NatEquality (suc m) zero = false
  NatEquality (suc m) (suc n) = NatEquality m n

  NatLess : Nat → Nat → Bool
  NatLess zero zero = false
  NatLess zero (suc n) = true
  NatLess (suc m) zero = false
  NatLess (suc m) (suc n) = NatLess m n

  -- Comparison, between two natural numbers--
  compare : Nat → Nat → Order
  compare zero zero = Equal
  compare zero (suc n) = Less
  compare (suc m) zero = Greater
  compare (suc m) (suc n) = compare m n

  --- Syntax part of miCro  ---

  -- Variables, with two arguments for name and value, are combined in a variable list to use as environment --
  -- could also change later to BoolVar, IntVar, etc for more variable types
  data Variable : Set where
    Var : String → Nat → Variable

  -- Heap is organized as a basic array of sorts, containing only nats
  -- It begins with zero length and is extended as necessary when values are added
  data Heap : Set where
    [h] : Heap
    _:H:_ : Nat → Heap → Heap

  infixr 5 _:H:_

  -- Environment holds the variables and their values
  data Env : Set where
    [e]  : Env
    _:e:_ : Variable → Env → Env

  infixr 5 _:e:_

  -- RAM uses the form "Env & Heap" for data.
  data RAM : Set where
    _&_ : Env → Heap → RAM

  infixr 5 _&_

  -- Helper function to return value from a given heap address --
  readHeapHelper : Heap → Nat → Nat
  readHeapHelper [h] x = zero
  readHeapHelper (n :H: h) zero = n
  readHeapHelper (n :H: h) (suc x) = readHeapHelper h x

  -- Helper function to return the total spaces occuppied in the heap
  heapSize : Heap → Nat
  heapSize [h] = zero
  heapSize (n :H: h) = suc (heapSize h)

  -- Expressions, used in comparisons or when assigning variables a value
  data Exp : Set where
    readVar : String → Exp
    plus : Exp → Exp → Exp
    const : Nat → Exp
    minus : Exp → Exp → Exp
    times : Exp → Nat → Exp

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
    IfElse : Cnd → Stmt → Stmt → Stmt
    While : Nat → Cnd → Stmt → Stmt
    AssignVar : String → Exp → Stmt
    ReadHeap : String → Exp → Stmt --writes the value at heap address Exp into the given var
    WriteHeap : Exp → Exp → Stmt --First exp is address, second is value (could also be nat → exp...?)
    New : String → Exp → Stmt -- Adds the value to the end of the current heap and makes a ptr var to it
    No-op : Stmt

  --- --- Evaluation functions, including eval (applied to programs) and it's helper functions --- ---

  --Reduce Exp, to simplify Exp to const values --
  {-# TERMINATING #-} -- For some reason adding heaps has broken the termination on this, even though it's basically still the same
  eval : RAM → Exp → Nat
  eval ([e] & h) (readVar str)  = zero -- If we can't find the variable we're trying to read, just return zero
  eval (((Var str2 x) :e: v) & h) (readVar str1) with primStringEquality str1 str2
  ...                                             | true = x
  ...                                             | false = eval (v & h) (readVar str1)
  eval r (const n) = n
  eval r (plus e1 e2) = (eval r e1) + (eval r e2)
  eval r (minus e1 e2) = (eval r e1) - (eval r e2)
  eval r (times e n) = (eval r e) * n

  -- Check, to reduce Cnd to boolean values --
  check : RAM → Cnd → Bool
  check r (Not c) with check r c
  ... | false = true
  ... | true = false
  check _ (cndBool b) = b
  check r (c1 And c2)  = boolAnd (check r c1) (check r c2)
  check r (c1 Or c2)  = boolOr (check r c1) (check r c2)
  check r (j == k)  with compare (eval r j) (eval r k)
  ... | Less = false
  ... | Equal = true
  ... | Greater = false
  check r (j != k) with compare (eval r j) (eval r k)
  ... | Less = true
  ... | Equal = false
  ... | Greater = true
  check r (j < k)  with compare (eval r j) (eval r k)
  ... | Less = true
  ... | Equal = false
  ... | Greater = false
  check r (j > k)  with compare (eval r j) (eval r k)
  ... | Less = false
  ... | Equal = false
  ... | Greater = true
  check r (j <= k) with compare (eval r j) (eval r k)
  ... | Less = true
  ... | Equal = true
  ... | Greater = false
  check r (j >= k) with compare (eval r j) (eval r k)
  ... | Less = false
  ... | Equal = true
  ... | Greater = true

  -- Update function, to write variables in environment --
  -- Heap not needed for this function, so I'm sticking with old implementation of env only
  -- Will apply the given type only if var is not found in env; otherwise old type remains
  update : Env  → String → Nat → Env
  update [e] str x = ((Var str x) :e: [e])
  update ((Var str1 n) :e: v) str2 x with primStringEquality str1 str2
  ... | true = ((Var str1 x) :e: v)
  ... | false = ((Var str1 n) :e: (update v str2 x))

  -- Write function, to write values into the heap at a specific address
  write : Heap → Nat → Nat → Heap
  write (n :H: h) zero x = (x :H: h)
  write (n :H: h) (suc a) x = n :H: (write h a x)
  write [h] zero x = (x :H: [h])
  write [h] (suc a) x = (zero :H: (write [h] a x))

  -- Add to heap function, appending the nat to the end of the heap
  addToHeap : Heap → Nat → Heap
  addToHeap [h] x = (x :H: [h])
  addToHeap (n :H: h) x = n :H: (addToHeap h x)


  -- Evaluation function, taking value of variable and code for input, producing value of variable at the end --
  {-# TERMINATING #-} --Doesn't read as terminating with the counter now as part of the while loop
  exec : RAM → Stmt → RAM
  exec r (Seq s1 s2) = exec (exec r s1) s2
  exec r (IfElse c s1 s2) with (check r c)
  ...                         | true = exec r s1
  ...                         | false = exec r s2
  exec r (While (suc n) c s) with (check r c)
  ... | false = r
  ... | true = exec r (Seq s (While n c s))
  exec r (While zero c s) = r
  exec (v & h) (AssignVar str e) = (update v str (eval (v & h) e)) & h
  exec (v & h) (WriteHeap e1 e2) = v & (write h (eval (v & h) e1) (eval (v & h) e2))
  exec (v & h) (ReadHeap str e) = (update v str (readHeapHelper h (eval (v & h) e))) & h
  exec (v & h) (New str e) = (update v str (heapSize h)) & (addToHeap h (eval (v & h) e))
  exec r No-op = r

  --- --- Test Programs --- ---
  -- Everything has to be written on one line I think since agda pays attention to white space --
  -- form is exec (code) (init x) ≡ expected outcome --
  -- Everything is nicely reflexive; intrinsic proofs I guess based on the typing? --

  {- readVar ++ is deprecated
  test1 : ∀ ( n : Nat ) → exec  (((Var "X" n) :e: [e]) & [h]) (Seq (AssignVar "X" (const 1)) (AssignVar "X" (readVar++ "X"))) ≡ ((Var "X" 2) :e: [e]) & [h]
  test1 n = refl
  -}

  test2 : exec ([e] & [h]) (IfElse ((readVar "X") == (const 0)) (AssignVar "X" (plus (readVar "X") (const 1))) No-op) ≡ ((Var "X" 1) :e: [e]) & [h]
  test2 = refl

  test3 : exec ([e] & [h]) (While 10 ((readVar "X") == (const 0)) (AssignVar "X" (plus (readVar "X") (const 1)))) ≡ ((Var "X" 1) :e: [e]) & [h]
  test3 = refl


  whileTest : exec ([e] & [h]) (While 10 ((readVar "X") < (const 10)) (AssignVar "X" (plus (const 1) (readVar "X")))) ≡ ((Var "X" 10) :e: [e]) & [h]
  whileTest = refl

  {- removed since now multiplication is only by const
  -- Can't do much without multiple vars, but this repeatedly X as long as it is less than or equal to 32 --
  greatestLesserPower : exec (((Var "X" 2) :e: [e]) & [h]) (While ((readVar "X") <= (const 32)) (AssignVar "X" (times (readVar "X") (readVar "X")))) ≡ ((Var "X" 256) :e: [e]) & [h]
  greatestLesserPower = refl
  -}

  -- Test with multiple Variables, based on Hoare Logic pdf from UW --

  {-This worked before; needs to be adjusted now that readVar ++ is no longer a thing
  UWEx1 : exec ([e] & [h]) (While ((readVar "k") <= (const 4)) (Seq (AssignVar "sum" (plus (readVar "k") (readVar "sum"))) (AssignVar "k" (readVar++ "k")))) ≡ ((Var "sum" 10) :e: (Var "k" 5) :e: [e]) & [h]
  UWEx1 = refl
  -}

  -- Heap Test: Basic read/write from heap; currently not working
  heapTest1 : exec ([e] & [h]) (Seq (New "x" (const 10)) (ReadHeap "y" (readVar "x"))) ≡ ((Var "x" 0) :e: (Var "y" 10) :e: [e]) & (10 :H: [h])
  heapTest1 = refl
-- To Add: Rules on equivalence of Env; if Env A contains Env B, then A ≡ B? or some similar relation, so that rhs of above statement/proofs can be condensed to only 1 variable --
