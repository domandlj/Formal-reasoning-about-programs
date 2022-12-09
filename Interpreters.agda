{-

  Juan S. Domandl
  2022
  Semantics of Arith exps, stack machine compiling 
-}

module Interpreters where
open import ADT.Stack.Stack
open import Data.List
open import Data.Maybe
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl;sym ; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Product using (_×_;_,_)
open import Data.Nat using (ℕ;zero;suc; _≡ᵇ_;_+_; _*_;_∸_) 
open import Data.Bool using (Bool; not; _∧_)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (yes; no)
--open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Function.Base using (case_of_; case_return_of_)


Var = String
Σ = Var → ℕ

∅ : Σ
∅ = (λ x → 0)

record Semantical (Exp Input Domain : Set) : Set₁ where
  field
    ⟦_⟧_ : Exp → Input → Domain

open Semantical {{...}} public

data BinOp : Set where
  _PLUS_ : BinOp
  _TIMES_ : BinOp
  _MINUS_ : BinOp

data Arith : Set where
  CONST : ℕ → Arith
  VAR : Var → Arith
  _PLUS_ : Arith → Arith → Arith
  _TIMES_ : Arith → Arith → Arith
  _MINUS_ : Arith → Arith → Arith


_[_/_] : Arith → Arith → Var → Arith
CONST n [ e / x ] = CONST n
VAR y [ e / x ] with y ≟ x
... | yes _ = e
... | no  _ = VAR y
(n PLUS m) [ e / x ] =  (n [ e / x ]) PLUS (m [ e / x ])
(n TIMES m) [ e / x ] =  (n [ e / x ]) TIMES (m [ e / x ])
(n MINUS m) [ e / x ] =  (n [ e / x ]) MINUS (m [ e / x ])


data ⊥ : Set where

_≢_ : {A : Set} → A → A → Set
a ≢ b = a ≡ b → ⊥


_[_↦_] : Σ → Var → ℕ → Σ
(σ [ X ↦ n ]) Y with Y ≟ X
... | yes _ = n
... | no  _ = σ Y

postulate
  axiom1 : ∀ (σ : Σ) (x : Var) (v : ℕ) 
  
    -------------------------------
    → (σ [ x ↦ v ]) x ≡ v 
  
  axiom2 : ∀ (σ : Σ) (x y : Var) (v : ℕ) 

        →  x ≢ y
    -------------------------------
    → (σ [ x ↦ v ]) y ≡ σ y

proof1 :  "x" ≢ "y"
proof1 = λ ()
proof2 :  "x" ≡ "x"
proof2 = refl



ℕ⟦_⟧_ : Arith → Σ → ℕ
ℕ⟦ CONST n ⟧ σ = n
ℕ⟦ VAR x ⟧ σ = σ x
ℕ⟦ n PLUS m ⟧ σ = ℕ⟦ n ⟧ σ + ℕ⟦ m ⟧ σ
ℕ⟦ n TIMES m ⟧ σ = ℕ⟦ n ⟧ σ * ℕ⟦ m ⟧ σ
ℕ⟦ n MINUS m ⟧ σ = ℕ⟦ n ⟧ σ ∸ ℕ⟦ m ⟧ σ

instance
  NatSemantical : Semantical Arith Σ ℕ
  NatSemantical = record { ⟦_⟧_ = ℕ⟦_⟧_ }

{-

  (e , σ) ----------------[e'/x]---------→  ( e [e'/x], σ)
        |                                       |
        |                                       |
      [ x ↦ ⟦ e' ⟧ σ ]                          ⟦_⟧ 
        |                                       |
        |                                       |  
        ↓                                       ↓
  (e , σ [ x ↦ ⟦ e' ⟧ σ ]) ----⟦_⟧-------→  ⟦ e [ e' / x ] ⟧ σ 
-}


subst-theorem : ∀ (e : Arith) {x : Var} {e' : Arith} {σ : Σ}

  ------------------------------------------------------
  → ℕ⟦ e [ e' / x ] ⟧ σ ≡  ℕ⟦ e ⟧ (σ [ x ↦ ℕ⟦ e' ⟧ σ ])
  

subst-theorem (CONST x) = refl
subst-theorem (VAR y) {x} with y ≟ x
... | yes _ = refl
... | no  _ = refl

subst-theorem (n PLUS m) {x} {e'} {σ}
  rewrite subst-theorem n {x} {e'} {σ}
        | subst-theorem m {x} {e'} {σ} = refl

subst-theorem (n TIMES m) {x} {e'} {σ}
  rewrite subst-theorem n {x} {e'} {σ}
        | subst-theorem m {x} {e'} {σ} = refl

subst-theorem (n MINUS m) {x} {e'} {σ}
  rewrite subst-theorem n {x} {e'} {σ}
        | subst-theorem m {x} {e'} {σ} = refl




{--
Notes about class types in agda. 

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

data Maybe (A : Set) : Set where
  nothing : Maybe A 
  just : A → Maybe A 


record Functor (F : Set → Set) : Set₁ where
  field
    fmap : ∀ {A B} → (A → B) → F A → F B
open Functor {{...}} public

map-list : {A B : Set} → (A → B) → List A → List B
map-list f nil = nil
map-list f (cons x xs) = cons (f x) (map-list f xs)

map-maybe : {A B : Set} → (A → B) → Maybe A → Maybe B
map-maybe f nothing = nothing
map-maybe f (just x) = just (f x)

instance
  ListFunctor : Functor (List)
  ListFunctor = record { fmap = map-list}

  MaybeFunctor : Functor (Maybe)
  MaybeFunctor = record { fmap = map-maybe}
--}



data Instruction : Set where 
  PUSH : ℕ → Instruction 
  ADD : Instruction
  MULT : Instruction
  SUB : Instruction

Program = List Instruction

-- this is just the (++) of lists
-- but lest prove some props about it
_⋈_ : Program → Program → Program
[] ⋈ p  = p
(x ∷ p') ⋈ p  = x ∷ ( p' ⋈ p)
infixr 5 _⋈_

⋈-neutral : ∀ (p : Program) → p ≡ p ⋈ []
⋈-neutral [] = refl
⋈-neutral (x ∷ p') 
  rewrite sym (⋈-neutral p') = refl 

⋈-assoc : ∀ (p1 p2 p3 : Program) → p1 ⋈ (p2 ⋈ p3) ≡ (p1 ⋈ p2) ⋈ p3
⋈-assoc [] p2 p3 = refl
⋈-assoc (x ∷ p1) p2 p3  
  rewrite ⋈-assoc p1 p2 p3 = refl

pushN : ℕ → Stack ℕ → Stack ℕ
pushN = push ℕ  

exec : Program → Stack ℕ → Stack ℕ
exec [] s = s
exec (PUSH x ∷ c) s = exec c (pushN x s)
exec (ADD ∷ c) (m ∷ n ∷ s) = exec c (pushN (n + m) s) 
exec (ADD ∷ c) _ = empty ℕ
exec (MULT ∷ c) (m ∷ n ∷ s) = exec c (pushN (n * m) s) 
exec (MULT ∷ c) _ = empty ℕ
exec (SUB ∷ c) (m ∷ n ∷ s) = exec c (pushN (n ∸ m) s) 
exec (SUB ∷ c) _ = empty ℕ


compile' : Arith → Σ → Program → Program
compile' (CONST n) σ c = PUSH n ∷ c
compile' (VAR x) σ c = PUSH (σ x) ∷ c
compile' (e1 PLUS e2) σ c = compile' e1 σ (compile' e2 σ (ADD ∷ c)) 
compile' (e1 TIMES e2) σ c = compile' e1 σ (compile' e2 σ (MULT ∷ c)) 
compile' (e1 MINUS e2) σ c = compile' e1 σ (compile' e2 σ (SUB ∷ c)) 

compile : Arith → Σ → Program
compile e σ = compile' e σ []

-- Example
program1 : Program 
program1 = 
    PUSH 2 ∷
    PUSH 5 ∷ 
    MULT   ∷
    PUSH 1 ∷
    ADD    ∷ 
    []

exp1 : Arith
exp1 = ((CONST 2) TIMES (CONST 5)) PLUS (CONST 1)

-- means
exp1-means = ℕ⟦ exp1 ⟧ ∅

-- compiled
p : Program
p = compile exp1 ∅

exec-p : Stack ℕ
exec-p = exec p (empty ℕ)


-- exec-p ≡ [ exp1-means ]
-- exec (compile exp1 ∅) (empty ℕ) ≡ [ ℕ⟦ exp1 ⟧ ∅ ] 
-- This fact is general.


compile'-correctness : ∀ (e : Arith) (σ : Σ) (s : Stack ℕ) (c : Program)
  
  ------------------------------------------------------
  → exec (compile' e σ c) s ≡ exec c (pushN (⟦ e ⟧ σ) s)

compile'-correctness (CONST n) σ s c = 
  begin
      exec (compile' (CONST n) σ c) s 
    ≡⟨⟩
      exec (PUSH n ∷ c) s 
    ≡⟨⟩
      exec c (pushN n s) 
    ≡⟨⟩
      exec c (pushN (⟦ (CONST n) ⟧ σ) s) 
  ∎

compile'-correctness (VAR x) σ s c = 
  begin
      exec (compile' (VAR x) σ c) s 
    ≡⟨⟩
      exec (PUSH ( σ x ) ∷ c) s 
    ≡⟨⟩
    exec c (pushN (σ x) s) 
    ≡⟨⟩
      exec c (pushN (⟦ (CONST (σ x)) ⟧ σ) s ) 
  ∎

compile'-correctness (e1 PLUS e2) σ s c =
  begin
      exec (compile' (e1 PLUS e2) σ c) s 
    ≡⟨⟩
      exec (compile' e1 σ (compile' e2 σ (ADD ∷ c))) s
    ≡⟨ compile'-correctness e1 σ s (compile' e2 σ (ADD ∷ c)) ⟩
      exec (compile' e2 σ (ADD ∷ c)) (pushN (⟦ e1 ⟧ σ) s )
    ≡⟨ compile'-correctness e2 σ (pushN (⟦ e1 ⟧ σ) s ) (ADD ∷ c) ⟩
      exec (ADD ∷ c) (pushN (⟦ e2 ⟧ σ) (pushN (⟦ e1 ⟧ σ) s ) ) 
    ≡⟨⟩
      exec c (pushN (⟦ e1 ⟧ σ + ⟦ e2 ⟧ σ) s ) 
    ≡⟨⟩
      exec c (pushN (⟦ (e1 PLUS e2) ⟧ σ) s ) 
  ∎

compile'-correctness (e1 TIMES e2) σ s c =
  begin
      exec (compile' (e1 TIMES e2) σ c) s 
    ≡⟨⟩
      exec (compile' e1 σ (compile' e2 σ (MULT ∷ c))) s
    ≡⟨ compile'-correctness e1 σ s (compile' e2 σ (MULT ∷ c)) ⟩
      exec (compile' e2 σ (MULT ∷ c)) (pushN (⟦ e1 ⟧ σ) s )
    ≡⟨ compile'-correctness e2 σ (pushN (⟦ e1 ⟧ σ) s ) (MULT ∷ c) ⟩
      exec (MULT ∷ c) (pushN (⟦ e2 ⟧ σ) (pushN (⟦ e1 ⟧ σ) s ) ) 
    ≡⟨⟩
      exec c (pushN (⟦ e1 ⟧ σ * ℕ⟦ e2 ⟧ σ) s ) 
    ≡⟨⟩
      exec c (pushN (⟦ (e1 TIMES e2) ⟧ σ) s ) 
  ∎

compile'-correctness (e1 MINUS e2) σ s c =
  begin
      exec (compile' (e1 MINUS e2) σ c) s 
    ≡⟨⟩
      exec (compile' e1 σ (compile' e2 σ (SUB ∷ c))) s
    ≡⟨ compile'-correctness e1 σ s (compile' e2 σ (SUB ∷ c)) ⟩
      exec (compile' e2 σ (SUB ∷ c)) (pushN (⟦ e1 ⟧ σ) s )
    ≡⟨ compile'-correctness e2 σ (pushN (⟦ e1 ⟧ σ) s ) (SUB ∷ c) ⟩
      exec (SUB ∷ c) (pushN (⟦ e2 ⟧ σ) (pushN (⟦ e1 ⟧ σ) s ) ) 
    ≡⟨⟩
      exec c (pushN (⟦ e1 ⟧ σ ∸ ⟦ e2 ⟧ σ) s ) 
    ≡⟨⟩
      exec c (pushN (⟦ (e1 MINUS e2) ⟧ σ) s ) 
  ∎


compile-correctness : ∀ (e : Arith) (σ : Σ) 

  ---------------------------------------------
  → exec (compile e σ) (empty ℕ) ≡ [ ⟦ e ⟧ σ ] 
    
compile-correctness e σ =
  begin
      exec (compile e σ) (empty ℕ)
    ≡⟨ compile'-correctness e σ (empty ℕ) [] ⟩ 
      exec [] (pushN (⟦ e ⟧ σ) (empty ℕ))
    ≡⟨⟩
      pushN (⟦ e ⟧ σ) (empty ℕ)
    ≡⟨⟩
      [ ⟦ e ⟧ σ ]
  ∎


{-
compile-correctness as a commutative diagram
          
        compile
Arith  --------→ Stack ℕ
     \           |
      \          |
 [⟦_⟧]  \         | exec 
        \        |
         \       |
          \      ↓
            → Stack ℕ
-}

data Cmd : Set where 
  SKIP   : Cmd
  _::=_ : Var → Arith → Cmd
  _::_ : Cmd → Cmd → Cmd
  REPEAT_DO_DONE : Arith → Cmd → Cmd

id : {A : Set} → A → A
id x = x 

_^_ : {A : Set } → (A → A) → ℕ → (A → A)
f ^ zero = id 
f ^ (suc n) = λ x → (f ^ n) (f x)

_∘_ : {A B C : Set } → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g (f x)

C⟦_⟧ : Cmd → Σ → Σ
C⟦ SKIP ⟧ σ = σ
C⟦ x ::= e ⟧ σ = σ [ x ↦ ⟦ e ⟧ σ ]
C⟦ c :: c' ⟧ σ = C⟦ c' ⟧ (C⟦ c ⟧ σ )
C⟦ REPEAT e DO c DONE ⟧ σ = (C⟦ c ⟧ ^ n) σ
  where
    n = ⟦ e ⟧ σ

infixr 5 _::_


fact-body : Cmd
fact-body = 
  "fact" ::= ((VAR "fact") TIMES (VAR "n")) ::
  "n" ::= ((VAR "n") MINUS (CONST 1))

fact' : Cmd
fact' = 
  "fact" ::= (CONST 1) ::
  REPEAT (VAR "n") DO
    fact-body
  DONE

input : Σ
input "n" = 5
input _ = 0
emp = C⟦ fact' ⟧ input 
j = emp "fact"

_! : ℕ → ℕ
zero ! = suc zero
(suc n) ! = (suc n) * n !

n*1≡n  : ∀ (n : ℕ) → n * 1 ≡ n 
n*1≡n zero = refl
n*1≡n (suc n) 
  rewrite n*1≡n n = refl

postulate
  σ-eq : ∀ {σ σ' : Σ} (x y : Var) 
   
   → σ x ≡ σ' x           → σ y ≡ σ' y
   -----------------------------------
        → σ ≡ σ'
  

body-correct : ∀ ( n fact : ℕ ) (σ : Σ) 
  
            → σ "n" ≡ n               → σ "fact" ≡ fact
  ------------------------------------------------------------------------
  →   (C⟦ fact-body ⟧ ^ n) σ ≡ (σ [ "n" ↦ 0 ]) [ "fact" ↦ (fact * (n !)) ]

body-correct zero fact σ σn≡n σfact≡fact
  rewrite (n*1≡n fact) =
  begin
    (C⟦ fact-body ⟧ ^ zero) σ
  ≡⟨ σ-eq "n" "fact" σn≡n σfact≡fact ⟩
    ((σ [ "n" ↦ 0 ]) [ "fact" ↦ fact ])
  ∎
body-correct (suc n) fact σ σsucn≡sucn σfact≡fact  =
  begin
    (C⟦ fact-body ⟧ ^ (suc n)) σ
  ≡⟨⟩
    (C⟦ fact-body ⟧ ^ n) (C⟦ fact-body ⟧ σ)
  ≡⟨⟩
     (C⟦ fact-body ⟧ ^ n) σ'
  ≡⟨ body-correct n (fact * suc n) σ' prop1 prop2 ⟩
   (σ' [ "n" ↦ 0 ]) [ "fact" ↦ ((fact * suc n) * (n !)) ]
  ≡⟨ prop3 σ' σ ⟩  
    (σ [ "n" ↦ 0 ]) [ "fact" ↦ fact * (suc n !) ]
  ∎
                                                              
  where
    σ' = (σ [ "fact" ↦ σ "fact" * σ "n" ]) 
        [ "n" ↦ (σ [ "fact" ↦ σ "fact" * σ "n" ]) "n" ∸ 1 ]
    
    σ'' = (σ [ "fact" ↦ σ "fact" * σ "n" ]) 
        [ "n" ↦ σ "n" ∸ 1 ]

    
    fact≢n : "fact" ≢ "n"
    fact≢n = λ () 
    
    prop0 : σ' ≡ (σ [ "fact" ↦ σ "fact" * σ "n" ]) 
        [ "n" ↦ σ "n" ∸ 1 ]
    prop0 
      rewrite axiom2 σ "fact" "n" (σ "fact" * σ "n") fact≢n = refl
    
    prop1 :  σ' "n" ≡ n
    prop1  
      rewrite prop0 
        | σsucn≡sucn  = refl
        
    prop2 :  σ' "fact" ≡ fact * suc n 
    prop2 
      rewrite prop0 
            | σfact≡fact 
            | σsucn≡sucn = refl
    
    postulate
      arith : fact * suc n * (n !) ≡ fact * ((n !) + n * (n !))
      -- this is simple arithmetic. 

    eqn : ∀ (σ1 σ2 : Σ) → ((σ1  [ "n" ↦ 0 ]) [ "fact" ↦ fact * suc n * (n !) ]) "n" ≡ 
      ((σ2  [ "n" ↦ 0 ]) [ "fact" ↦ fact * ((n !) + n * (n !)) ]) "n"
    eqn σ1 σ2
      rewrite axiom2 σ1 "fact" "n" (fact * suc n * (n !)) fact≢n 
        |     axiom2 σ2 "fact" "n" (fact * suc n * (n !)) fact≢n = refl

    eqfact : ∀ (σ1 σ2 : Σ) → ((σ1  [ "n" ↦ 0 ]) [ "fact" ↦ fact * suc n * (n !) ]) "fact" ≡ 
      ((σ2  [ "n" ↦ 0 ]) [ "fact" ↦ fact * ((n !) + n * (n !)) ]) "fact"
    eqfact σ1 σ2
      rewrite axiom2 σ1 "fact" "n" (fact * suc n * (n !)) fact≢n 
        |     axiom2 σ2 "fact" "n" (fact * suc n * (n !)) fact≢n 
        |      arith = refl

    prop3 : ∀ (σ1 σ2 : Σ) → ((σ1 [ "n" ↦ 0 ]) [ "fact" ↦ fact * suc n * (n !) ]) ≡ 
        ((σ2 [ "n" ↦ 0 ]) [ "fact" ↦ fact * ((n !) + n * (n !)) ])
    prop3 σ1 σ2 
      rewrite σ-eq 
        {((σ1 [ "n" ↦ 0 ]) [ "fact" ↦ fact * suc n * (n !) ])} 
        {((σ2 [ "n" ↦ 0 ]) [ "fact" ↦ fact * ((n !) + n * (n !)) ])} 
        "n" "fact" (eqn  σ1 σ2) (eqfact σ1 σ2) = refl
      
      
      
       
  
    


    
