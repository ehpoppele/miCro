--Main file for definition of a Hoare Triple, using the micro Language
--Contains the type definition for Hoare Triples and for the symbolic environments that are used to verify them
--Also contains all the functions used that deal with Symbolic Environments
--Other functions used here that deal only with Cnds or Exps are in the relevant file in the Semantics folder
module HoareTriples where

  open import Language.miCro
  open import Language.miCro_parser
  open import Semantics.Expressions
  open import Semantics.Conditions
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open import Agda.Builtin.Bool

  --Symbolic Environments represent a set of possible states that the program could be in at any time
  --It does this by joining restrictions on variables with And or Or
  data SymbolicEnv : Set where
    _<S_ : Exp → Exp → SymbolicEnv
    _<=S_ : Exp → Exp → SymbolicEnv
    _>S_ : Exp → Exp → SymbolicEnv
    _>=S_ : Exp → Exp → SymbolicEnv
    _==S_ : Exp → Exp → SymbolicEnv
    _!=S_ : Exp → Exp → SymbolicEnv
    trueS : SymbolicEnv --Represents the set of all possible states; should not be joined to anything with andS/orS
    falseS : SymbolicEnv --Represents the set of no states; should not be joined to any other SEnv
    _andS_ : SymbolicEnv → SymbolicEnv → SymbolicEnv
    _orS_ : SymbolicEnv → SymbolicEnv → SymbolicEnv

  --Combines two SEnvs with an andS, following appropriate rules for true/false and keeping orS at the top level
  CombineEnv : SymbolicEnv → SymbolicEnv → SymbolicEnv
  CombineEnv falseS e = falseS
  CombineEnv e falseS = falseS
  CombineEnv trueS e = e
  CombineEnv e trueS = e
  CombineEnv (e1 orS e2) e3 = (CombineEnv e1 e3) orS (CombineEnv e2 e3)
  CombineEnv e1 (e2 orS e3) = (CombineEnv e1 e2) orS (CombineEnv e1 e3)
  CombineEnv e1 e2 = e1 andS e2

--Finds state sets complying with the given condition; handles Or then passes off the rest
--Essentially transforms a Cnd into a the minimum formula which upholds the Cnd
  StatesSatisfying : Cnd → SymbolicEnv
  StatesSatisfying (c1 Or c2) = (StatesSatisfying c1) orS (StatesSatisfying c2)
  StatesSatisfying (cndBool true) = trueS
  StatesSatisfying (cndBool false) = falseS
  StatesSatisfying (c1 And c2) = CombineEnv (StatesSatisfying c1) (StatesSatisfying c2)
  StatesSatisfying ((times (readVar str) k) == e) = ((times (readVar str) k) ==S e)
  StatesSatisfying ((times (readVar str) k) < e) = ((times (readVar str) k) <S e)
  StatesSatisfying ((times (readVar str) k) <= e) = ((times (readVar str) k) <=S e)
  StatesSatisfying ((times (readVar str) k) > e) = ((times (readVar str) k) >S e)
  StatesSatisfying ((times (readVar str) k) >= e) = ((times (readVar str) k) >=S e)
  StatesSatisfying ((times (readVar str) k) != e) = ((times (readVar str) k) !=S e)
  StatesSatisfying other = falseS --Currently not allowing any other conditions to keep it simple

  --Returns a modified version of the given condition, where the given SEnv is taken into account as a restriction
  -- Currently these will sometimes lose their canonical form, which may be an issue, but so far isn't
  -- I don't think this function itself relies on the form, however, so maybe can be fixed
  -- By just doing canonicalization later; before AlwaysTrue is evaluated?
  --This also currently fails, since it will skip a restriction if it none of its variables appear in the Cnd
  --And then will not return to that SEnv if other variables were added to the Cnd to make the first restriction relevant
  ModifyCnd : SymbolicEnv → Cnd → Cnd
  ModifyCnd s (cndBool true) = (cndBool true)
  ModifyCnd s (cndBool false) = (cndBool false)
  ModifyCnd s (c1 Or c2) = (ModifyCnd s c1) Or (ModifyCnd s c2) --We shouldn't be getting either of these cases based on how this is used in SEnvSatisfies
  ModifyCnd s (c1 And c2) = (ModifyCnd s c1) And (ModifyCnd s c2) --But I'm writing them out in case for clarity and in case this function is later used for anything else
  ModifyCnd ((times (readVar var) k) ==S e1) c = ReplaceInCnd k var e1 c
  ModifyCnd ((times (readVar var) k) !=S e1) c with CndContainsVar var c
  ... | true = c And ((times (readVar var) k) != e1)
  ... | false = c
  ModifyCnd ((times (readVar var) k) <S e1) (e2 == e3) with WhichSideContainsVar var (e2 == e3)
  ... | Left = (e2 == e3) And (ReplaceInCnd k var (minus e1 (const 1)) ((plus e2 (const 1)) > e3))
  ... | Right = (e2 == e3) And (ReplaceInCnd k var (minus e1 (const 1)) (e2 < (plus e3 (const 1)))) --trust me this works
  ... | NoSide = (e2 == e3)
  ModifyCnd ((times (readVar var) k) <S e1) (e2 < e3) with WhichSideContainsVar var (e2 < e3)
  ... | Left = (e2 < e3) Or (ReplaceInCnd k var (minus e1 (const 1)) (e2 < e3)) --No plus one like before since we're dealing with a strict less than
  ... | Right = (e2 < e3) And (ReplaceInCnd k var (minus e1 (const 1)) (e2 < e3))
  ... | NoSide = (e2 < e3)
  ModifyCnd ((times (readVar var) k) <S e1) (e2 > e3) with WhichSideContainsVar var (e2 > e3)
  ... | Left = (e2 > e3) And (ReplaceInCnd k var (minus e1 (const 1)) (e2 > e3))
  ... | Right = (e2 > e3) Or (ReplaceInCnd k var (minus e1 (const 1)) (e2 > e3))
  ... | NoSide = (e2 > e3)
  ModifyCnd ((times (readVar var) k) >S e1) (e2 == e3) with WhichSideContainsVar var (e2 == e3)
  ... | Left = (e2 == e3) And (ReplaceInCnd k var (plus e1 (const 1)) ((minus e2 (const 1)) < e3))
  ... | Right = (e2 == e3) And (ReplaceInCnd k var (plus e1 (const 1)) (e2 > (minus e3 (const 1)))) --trust me this works
  ... | NoSide = (e2 == e3)
  ModifyCnd ((times (readVar var) k) >S e1) (e2 > e3) with WhichSideContainsVar var (e2 > e3)
  ... | Left = (e2 > e3) Or (ReplaceInCnd k var (plus e1 (const 1)) (e2 > e3))
  ... | Right = (e2 > e3) And (ReplaceInCnd k var (plus e1 (const 1)) (e2 > e3))
  ... | NoSide = (e2 > e3)
  ModifyCnd ((times (readVar var) k) >S e1) (e2 < e3) with WhichSideContainsVar var (e2 < e3)
  ... | Left = (e2 < e3) And (ReplaceInCnd k var (plus e1 (const 1)) (e2 < e3))
  ... | Right = (e2 < e3) Or (ReplaceInCnd k var (plus e1 (const 1)) (e2 < e3))
  ... | NoSide = (e2 < e3)
  ModifyCnd vr c = c --The Env at this point should be a comparison between a var and expression, so we shouldn't reach these cases


  --Will return false if there is any state from the SymbolicEnv in which Cnd does not hold, and true otherwise
  --The idea here is that state restrictions (comparisons) are consumed and used to modify the condition until they are all "absorbed"
  --Where the condition will now read as AlwaysTrue if the it met the restrictions (eg, rstr x = 4, cnd x < 5 becomes cnd 4 < 5, reads as AlwaysTrue)
  {-# TERMINATING #-}
  SEnvSatisfiesCnd : SymbolicEnv → Cnd → Bool
  SEnvSatisfiesCnd falseS c = true
  SEnvSatisfiesCnd trueS c = (AlwaysTrue c)
  SEnvSatisfiesCnd (e1 orS e2) c =  boolAnd (SEnvSatisfiesCnd e1 c) (SEnvSatisfiesCnd e2 c)
  SEnvSatisfiesCnd (e1 andS e2) c = SEnvSatisfiesCnd e2 (ModifyCnd e1 c) --Assuming the Envs are in proper form, e1 will be an atomic and e2 could be an atomic or another and
  SEnvSatisfiesCnd comp c = SEnvSatisfiesCnd trueS (ModifyCnd comp c) --All other symbolic constructors are comparisons, so we

  --An object which provides evidence that the predicate holds in all states in the state set
  data ConditionHolds : SymbolicEnv → Cnd → Set where
    ConditionHoldsProof : ∀ {st : SymbolicEnv} {c : Cnd}
      → (SEnvSatisfiesCnd st c ≡ true)
      -----------------------------
      → ConditionHolds st c

  --New type used for symbolic check function
  --Always is for when the Cnd is always true in all states represented by the symbolicEnv
  --Never is similar, and Sometimes is when it holds in some but not all of the states (eg, SE is x < 4, cnd is x == 2)
  data HoldsWhen : Set where
    Always : HoldsWhen
    Sometimes : HoldsWhen
    Never : HoldsWhen

  --Helper function for when the condition could be Never or Sometimes
  SymbolicCheck2 : SymbolicEnv → Cnd → HoldsWhen
  SymbolicCheck2 env c with SEnvSatisfiesCnd env (FlipCnd c) --Need this in canonical form
  ... | true = Never
  ... | false = Sometimes

  -- Symbolic version of the check function
  SymbolicCheck : SymbolicEnv → Cnd → HoldsWhen
  SymbolicCheck falseS c = Never --I'm not sure this is right at all, but if we have false at any point we will have false at the end so it doesn't matter
  SymbolicCheck env c with SEnvSatisfiesCnd env c
  ... | true = Always
  ... | false = SymbolicCheck2 env c

  --Renames all instances of string in the given env by appending the nat to them
  --Assumes that the Env is a comparison type; currently does not work for other forms
  LVarRename : Nat → SymbolicEnv → String → SymbolicEnv
  LVarRename n (e1 ==S e2) str = ((RenameInExp n e1 str) ==S (RenameInExp n e2 str))
  LVarRename n (e1 <S e2) str = ((RenameInExp n e1 str) <S (RenameInExp n e2 str))
  LVarRename n (e1 <=S e2) str = ((RenameInExp n e1 str) <=S (RenameInExp n e2 str))
  LVarRename n (e1 >S e2) str = ((RenameInExp n e1 str) >S (RenameInExp n e2 str))
  LVarRename n (e1 >=S e2) str = ((RenameInExp n e1 str) >=S (RenameInExp n e2 str))
  LVarRename n (e1 !=S e2) str = ((RenameInExp n e1 str) !=S (RenameInExp n e2 str))
  LVarRename n e str = e

  --Adds to the current env and then renames all old variables if a variable is reassigned
  --these are the "Lvars"; if X is used in env and then is reassigned, it will be "x" + "[nat]"
  SymbolicUpdate : Nat → SymbolicEnv → String → Exp → SymbolicEnv
  SymbolicUpdate n falseS str e = falseS
  SymbolicUpdate n trueS str e = ((times (readVar str) 1) ==S (RenameInExp n e str))
  SymbolicUpdate n (env1 orS env2) str e = ((SymbolicUpdate n env1 str (RenameInExp n e str)) orS (SymbolicUpdate n env2 str (RenameInExp n e str)))
  SymbolicUpdate n (env1 andS env2) str e = ((LVarRename n env1 str) andS (SymbolicUpdate n env2 str (RenameInExp n e str))) --We are going to append the exp to the last Env in the and, so we only need to do renaming for the first of the two
  SymbolicUpdate n comp str e = (LVarRename n comp str) andS ((times (readVar str) 1) ==S (RenameInExp n e str))

  -- Functions similar to exec, but different rules on changing the Env; also while is not allowed at present (is skipped over)
  -- the Nat used is an LVar counter, increased with each new instruction
  SymbolicExec : Nat → SymbolicEnv → Stmt → SymbolicEnv
  SymbolicExec n env (Seq s1 s2) = SymbolicExec (suc n) (SymbolicExec n env s1) s2
  SymbolicExec n env (IfElse c s1 s2) with (SymbolicCheck env c)
  ...                         | Always = SymbolicExec n env s1
  ...                         | Never = SymbolicExec n env s2
  ...                         | Sometimes = (SymbolicExec n env s1) orS (SymbolicExec n env s2) --Join cnd to respective env
  SymbolicExec n env (While zero c s) = env
  SymbolicExec n env (While (suc n2) c s)  with (SymbolicCheck env c)
  ... | Never = env
  ... | Always = SymbolicExec n env (Seq s (While n2 c s))
  ... | Sometimes = (env) orS (SymbolicExec n env (Seq s (While n2 c s)))
  SymbolicExec n env (AssignVar str e) = (SymbolicUpdate n env str e)
  SymbolicExec n env other = env --Heaps ops currently not allowed



  --The actual Hoare Triple type; requires a ConditionHolds object as proof
  --For most concrete triples (all values explicit, no "∀" etc) this will often be a refl proof
  --Works at present for most cases, but has issue with CFCnd and ModifyCnd
  data HoareTriple : Cnd → Stmt → Cnd → Set where
    HTSymbolicEnvProof : ∀ {c1 c2 : Cnd} {s : Stmt}
      → (ConditionHolds (SymbolicExec 1 (StatesSatisfying (CFCnd c1)) s) (CFCnd c2)) --The 1 is the default for lvar counter
      ---------------------------
      → HoareTriple c1 s c2

  syntax HoareTriple c1 s c2 = [ c1 ] s [ c2 ] --Curly brackets reserved for something else, so we use square instead
  
