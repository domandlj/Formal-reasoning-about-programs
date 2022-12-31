# Formal-reasoning-about-programs

Work in progress, i'm trying to mechanize the book "Formal Reasoning About Programs" of Adam Chlipala in Agda instead of Coq. Not following it exactly though, adding some things and ommiting others.  

# Files 
| **File (Dir)**          | **Chapter** | **Contnent**                                                                                                                                                                                                                                                                                                                                         |
| ----------------------- | ----------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Syntax.agda`           | **2**       | Abstract syntax of int expressions.                                                                                                                                                                                                                                                                                                                  |
| `ADT`                   | **3**       | Abstract data types as existential types, verification of a Queue, auxilar Stack                                                                                                                                                                                                                                                                     |
| `Interpreters.agda`     | **4**       | Denotational semantics of int expressions and a compiler to a stack machine,     Correctness of compiler exec with respect to denotational semantics.   Denotational semantics of an primitive recursive imperative language,   Correctness of imperative factorial and wrt specification. Using type classes to overload the denotational function. |
| `Relations.agda`        | **5**       | Relations as types. Relations: transitive closure and permutation.                                                                                                                                                                                                                                                                                   |
| `TransitionSystem.agda` | **6**       | Programs as state machines.                                                                                                                                                                                                                                                                                                                          |
| `ModelCheck.agda`       | **7**       | Automatic way to get ts invariants                                                                                                                                                                                                                                                                                                                   |


# Automation
For now just using Z3 via schmitty for a decidable theory of naturals. 

# Requirements
`schmitty`
