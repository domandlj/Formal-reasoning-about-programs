{-

  Juan S. Domandl
  2022
  Abstract Data Types, specification and existential types.

-}

module Interpreters where
open import ADT.Stack.Stack
open import Data.List
open import Data.Maybe
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl;sym ; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Product using (_×_;_,_)
open import Data.Nat using (ℕ; _+_; _*_;_∸_) 
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



_[_↦_] : Σ → Var → ℕ → Σ
(σ [ X ↦ n ]) Y with Y ≟ X
... | yes _ = n
... | no  _ = σ Y


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


compile'-correctnes : ∀ (e : Arith) (σ : Σ) (s : Stack ℕ) (c : Program)
  
  ------------------------------------------------------
  → exec (compile' e σ c) s ≡ exec c (pushN (⟦ e ⟧ σ) s)

compile'-correctnes (CONST n) σ s c = 
  begin
      exec (compile' (CONST n) σ c) s 
    ≡⟨⟩
      exec (PUSH n ∷ c) s 
    ≡⟨⟩
      exec c (pushN n s) 
    ≡⟨⟩
      exec c (pushN (⟦ (CONST n) ⟧ σ) s) 
  ∎

compile'-correctnes (VAR x) σ s c = 
  begin
      exec (compile' (VAR x) σ c) s 
    ≡⟨⟩
      exec (PUSH ( σ x ) ∷ c) s 
    ≡⟨⟩
    exec c (pushN (σ x) s) 
    ≡⟨⟩
      exec c (pushN (⟦ (CONST (σ x)) ⟧ σ) s ) 
  ∎

compile'-correctnes (e1 PLUS e2) σ s c =
  begin
      exec (compile' (e1 PLUS e2) σ c) s 
    ≡⟨⟩
      exec (compile' e1 σ (compile' e2 σ (ADD ∷ c))) s
    ≡⟨ compile'-correctnes e1 σ s (compile' e2 σ (ADD ∷ c)) ⟩
      exec (compile' e2 σ (ADD ∷ c)) (pushN (⟦ e1 ⟧ σ) s )
    ≡⟨ compile'-correctnes e2 σ (pushN (⟦ e1 ⟧ σ) s ) (ADD ∷ c) ⟩
      exec (ADD ∷ c) (pushN (⟦ e2 ⟧ σ) (pushN (⟦ e1 ⟧ σ) s ) ) 
    ≡⟨⟩
      exec c (pushN (⟦ e1 ⟧ σ + ⟦ e2 ⟧ σ) s ) 
    ≡⟨⟩
      exec c (pushN (⟦ (e1 PLUS e2) ⟧ σ) s ) 
  ∎

compile'-correctnes (e1 TIMES e2) σ s c =
  begin
      exec (compile' (e1 TIMES e2) σ c) s 
    ≡⟨⟩
      exec (compile' e1 σ (compile' e2 σ (MULT ∷ c))) s
    ≡⟨ compile'-correctnes e1 σ s (compile' e2 σ (MULT ∷ c)) ⟩
      exec (compile' e2 σ (MULT ∷ c)) (pushN (⟦ e1 ⟧ σ) s )
    ≡⟨ compile'-correctnes e2 σ (pushN (⟦ e1 ⟧ σ) s ) (MULT ∷ c) ⟩
      exec (MULT ∷ c) (pushN (⟦ e2 ⟧ σ) (pushN (⟦ e1 ⟧ σ) s ) ) 
    ≡⟨⟩
      exec c (pushN (⟦ e1 ⟧ σ * ℕ⟦ e2 ⟧ σ) s ) 
    ≡⟨⟩
      exec c (pushN (⟦ (e1 TIMES e2) ⟧ σ) s ) 
  ∎

compile'-correctnes (e1 MINUS e2) σ s c =
  begin
      exec (compile' (e1 MINUS e2) σ c) s 
    ≡⟨⟩
      exec (compile' e1 σ (compile' e2 σ (SUB ∷ c))) s
    ≡⟨ compile'-correctnes e1 σ s (compile' e2 σ (SUB ∷ c)) ⟩
      exec (compile' e2 σ (SUB ∷ c)) (pushN (⟦ e1 ⟧ σ) s )
    ≡⟨ compile'-correctnes e2 σ (pushN (⟦ e1 ⟧ σ) s ) (SUB ∷ c) ⟩
      exec (SUB ∷ c) (pushN (⟦ e2 ⟧ σ) (pushN (⟦ e1 ⟧ σ) s ) ) 
    ≡⟨⟩
      exec c (pushN (⟦ e1 ⟧ σ ∸ ⟦ e2 ⟧ σ) s ) 
    ≡⟨⟩
      exec c (pushN (⟦ (e1 MINUS e2) ⟧ σ) s ) 
  ∎


compile-correctnes : ∀ (e : Arith) (σ : Σ) 

  ---------------------------------------------
  → exec (compile e σ) (empty ℕ) ≡ [ ⟦ e ⟧ σ ] 
    
compile-correctnes e σ =
  begin
      exec (compile e σ) (empty ℕ)
    ≡⟨ compile'-correctnes e σ (empty ℕ) [] ⟩ 
      exec [] (pushN (⟦ e ⟧ σ) (empty ℕ))
    ≡⟨⟩
      pushN (⟦ e ⟧ σ) (empty ℕ)
    ≡⟨⟩
      [ ⟦ e ⟧ σ ]
  ∎