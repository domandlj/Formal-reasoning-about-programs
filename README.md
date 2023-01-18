# Formal reasoning about programs

Work in progress, i'm trying to mechanize the book "Formal Reasoning About Programs" of Adam Chlipala in Agda instead of Coq. Not following it exactly though, adding some things and ommiting others.  

# Files 
| **File (Dir)**          | **Chapter** | **Content**                                                                                                                                                                                                                                                                                                                                          |
| ----------------------- | ----------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Syntax.agda`           | **2**       | Abstract syntax of int expressions.                                                                                                                                                                                                                                                                                                                  |
| `ADT`                   | **3**       | Abstract data types as existential types, verification of a Queue, auxilar Stack                                                                                                                                                                                                                                                                     |
| `Interpreters.agda`     | **4**       | Denotational semantics of int expressions and a compiler to a stack machine,     Correctness of compiler exec with respect to denotational semantics.   Denotational semantics of an primitive recursive imperative language,   Correctness of imperative factorial and wrt specification. Using type classes to overload the denotational function. |
| `Relations.agda`        | **5**       | Relations as types. Relations: transitive closure and permutation.                                                                                                                                                                                                                                                                                   |
| `TransitionSystem.agda` | **6**       | Programs as state machines.                                                                                                                                                                                                                                                                                                                          |
| `ModelCheck.agda`       | **7**       | Automatic way to get ts invariants                                                                                                                                                                                                                                                                                                                   |

# Misc
| **File (Dir)**               | **Content**                                                                                              |
| ---------------------------- | -------------------------------------------------------------------------------------------------------- |
| `InternalExternalVerif.agda` | Verification of functional programs, internal or external                                                |
| `Tarski.agda`                | Denotational semantics of imperative lang in relational style. Proof of  Knaster–Tarski fixpoint theorem |
| `Cats.agda`                  | Some category theory                                                                                     |


# Automation
For now just using Z3 via schmitty for a decidable theory of naturals. 

# Books about PL theory and formal methods in proof assistants.
| **Book**                                         | **Proof assistant** | **Authors**                                                                         |
| ------------------------------------------------ | ------------------- | ----------------------------------------------------------------------------------- |
| `Software Foundations`                           | **Coq**             | Benjamin C. Pierce, a lot more.                                                     |
| `Formal Reasoning About Programs`                | **Coq**             | Adam Chlipala.                                                                      |
| `Certified Programming with Dependent Types`     | **Coq**             | Adam Chlipala.                                                                      |
| `Programming Language Foundations in Agda`       | **Agda**            | Philip Wadler and Wen Kokke and Jeremy G. Siek.                                     |
| `Verified Functional Programming in Agda`        | **Agda**            | Aaron Stump.                                                                        |
| `Type-Driven Development with  Idris`            | **Idris**           | Edwin Brady.                                                                        |
| `Concrete Semantics: With Isabelle/HOL`          | **Isabelle/HOL**    | Tobias Nipkow, Gerwin Klein.                                                        |
| `The Hitchhiker’s Guide to Logical Verification` | **Lean**            | Anne Baanen, Alexander Bentkamp, Jasmin Blanchette, Johannes Hölzl, Jannis Limperg. |
|                                                  |                     |                                                                                     |
# Requirements
`schmitty`
