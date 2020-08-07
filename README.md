# miCro

### An Attempt to Implemente Hoare Triples in Agda

This project features a nearly-complete implementation of Hoare Triples in Agda, acting on code segments and predicates written in a very minimal C-style language (miCro), which is also implemented in Agda.

A short presentation (in the form of LaTeX slides) will be added to succintly describe the project.

#### Files

The Language folder contains the implementation of the miCro language, featuring an interpreter, a recursive descent parser, and a tokenizer, as well as some test files for each of these.

The Semantics folder contains Expression and Condition files, along with tests for each. These implement many functions relating to the two data types that are used in Hoare Triple verification, primarily the functions used to convert each type to a "canonical form." The goal of the canonical form is one which is easy to handle in other functions and also very standard, so that all mathematically equivalent Expressions and logically equivalent Conditions will canonicalize to the same form. This is successful for Expressions but not entirely for conditions, as detailed in the documentation.

The Old Versions folder contains  several previous implementations including a miCro language with no heap memory, a non-recursive descent parser, and less successful versions of the Hoare Triples. 

The main project folder also includes the Hoare Triple file and an Example file which includes a few tests and proofs of this Hoare Triple Implementation. The main Hoare Triple file includes the definition of the triple as a data type, as well as the symbolic environments and the functions which act on them to verify the correctness of a triple.

#### The Language

The language uses C-style syntax and includes variable assignment, if-else statements, while loops, and heap operations. The heap operations are reading from the heap into a variable, writing to a specific location in the heap, or adding a New value to the end of the current heap. 

If-else and while statements take a condition as the first argument, which can be a boolean or a comparison between two expressions (using <, >, <=, >=, !=, or ==), and conditions may also be joined with an Or or an And or modified with Not.

Expressions are used for Condition comparisons, variable assignments, or writing to the heap. They include only natural numbers and variable reads, and can be joined by plus or minus (minus always giving zero as a minimum value). Times can also be used in an expression, but applies to only a single expression, multiplying it by a constant natural number (multiplication by variables or more complicated expressions is not allowed).

#### Hoare Triples

The Hoare Triples are implemented as a data type which takes one pre-Condition, one Stmt to execute, and one post-Condition. The current constructor for the triple takes a ConditionHolds object as proof, which is another object that takes a SymbolicEnv and a Condition, and provides proof that the Condition holds in all possible states that the SymbolicEnv represents. In this case, the SymbolicEnv represents the "end state" after applying the Stmt to the pre-Condition, while the Condition used in the ConditionHolds object will be the same as the post-Condition.

The SymbolicEnv is another data type, which is used to represent a set of states during the execution of a block of code. Its structure is very similar to that of the Condition type, with the idea being that it is a boolean state or a collection of comparisons, which are used to represent the restrictions on variables in the current state. For example, the SymbolicEnv "x < 3 And y == 4" would represent the set of all states where y has a value of 4 and x has a value less than 3, while all other variables may have any value. The boolean state true represents the set of all possible states, where no conclusions may be drawn about the values of any variables, while the boolean state false represents an absurdity, indicating a set of restrictions which no states can satisfy (such as x < 3 And x > 4). In this way it is sort of an "empty set" of states.

In the HoareTriple constructor, the pre-Condition is transformed into a SymbolicEnv, and the code block is then run on this Env to produce another SymbolicEnv, representing the set of "end states." The ConditionHolds object then provides proof that these end states satisfy the post-Condition, which then proves the triple to be valid. For the ConditionHolds object to do this, it requires proof that the "end states" SymbolicEnv satisfies the post-Condition, by making a call to a function (SEnvSatisfiesCnd) which takes the two and returns a boolean. For most explicit Hoare Triples (where all variables are defined, and no "for all"s are used), this proof is often satisfied with refl, as the functions will confirm that the triple is valid.

To check if a SymbolicEnv satisfies a given Condition, the comparisons in the Env are "absorbed" into the Condition until the condition contains all the relevant restrictions or values of variables. Another function is then run to check if this combined condition is always true, regardless of the values of its variables, and that then provides a boolean as the final response. For example, if the condition is x < 3, and the SymbolicEnv is (x == 2 And y > 4), then the Condition will be modified by the first comparison to become 2 < 3, while ignoring the second one since it contains no relevant variables. 2 < 3 would then easily be verified as being AlwaysTrue. If the SymbolicEnv were instead (x == 2 Or y > 4), the Condition would become (2 < 3 Or x < 3), which is not always true.
This function does not work properly in all cases, and requires some modification before it can behave as described above in all cases.


