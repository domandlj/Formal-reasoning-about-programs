module Denotational where
import Relation.Binary.PropositionalEquality as Eqq
open import Data.Nat using (ℕ; zero; suc; _+_;_∸_; _*_)
open import Data.Product using (_×_;_,_)
open import Data.List
open import Data.Maybe
open import Data.List.Relation.Unary.Any
open import Data.Bool using (true; false; _∧_; Bool; if_then_else_)
open Eqq using (_≡_; refl; cong; cong₂; sym ; trans)
open Eqq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Product
open import Data.String using (String; _≟_)
open import Relation.Nullary using (yes; no)
open import Data.Sum.Base

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {x : ℕ}
    
    ----------
    → zero ≤ x

  s≤s : ∀ {x y : ℕ}
    
        → x ≤  y
    --------------------
    → (suc x) ≤ (suc y)

x≤y⇒x≤sy : ∀ {x y : ℕ} 
  
    → x ≤ y 
  ------------
  → x ≤ suc y
x≤y⇒x≤sy z≤n = z≤n
x≤y⇒x≤sy (s≤s r) = s≤s (x≤y⇒x≤sy r)  


record Eq {a} (A : Set a) : Set a where
  field
    _==_ : A → A → Bool

open Eq {{...}} public

natEquals : ℕ → ℕ → Bool
natEquals zero zero = true
natEquals (suc n) (suc m) = natEquals n m
natEquals _  _ = false

instance
  eqList : ∀ {a} {A : Set a} → {{Eq A}} → Eq (List A)
  _==_ {{eqList}} []       []       = true
  _==_ {{eqList}} (x ∷ xs) (y ∷ ys) = x == y ∧ xs == ys
  _==_ {{eqList}} _        _        = false

  eqNat : Eq ℕ
  _==_ {{eqNat}} = natEquals

-- In set theory:  for a set A and P a predicate over A (i.e. P ⊆ A), S = {x ∈ A | P x }
-- In type theory: A : Set, P : A → Set and  S = Σ A P  


-- {n : ℕ | 4 ≤ n}, here ℕ is the set and less than four the predicate.

m : Σ ℕ (λ n → 4 ≤ n)
m = 5 , s≤s (s≤s (s≤s (s≤s z≤n)))

Var = String
Σ' = Var → ℕ

data Boolean : Set where
  TRUE : Boolean
  FALSE : Boolean


data Arith : Set where
  CONST : ℕ → Arith
  VAR : Var → Arith
  _PLUS_ : Arith → Arith → Arith
  _TIMES_ : Arith → Arith → Arith
  _MINUS_ : Arith → Arith → Arith


data Cmd : Set where 
  SKIP   : Cmd
  _::=_ : Var → Arith → Cmd
  _::_ : Cmd → Cmd → Cmd
  WHILE_DO_DONE : Boolean → Cmd → Cmd

_[_/_] : Arith → Arith → Var → Arith
CONST n [ e / x ] = CONST n
VAR y [ e / x ] with y ≟ x
... | yes _ = e
... | no  _ = VAR y
(n PLUS m) [ e / x ] =  (n [ e / x ]) PLUS (m [ e / x ])
(n TIMES m) [ e / x ] =  (n [ e / x ]) TIMES (m [ e / x ])
(n MINUS m) [ e / x ] =  (n [ e / x ]) MINUS (m [ e / x ])


_[_↦_] : Σ' → Var → ℕ → Σ'
(σ [ X ↦ n ]) Y with Y ≟ X
... | yes _ = n
... | no  _ = σ Y

ℕ⟦_⟧ : Arith → Σ' → ℕ
ℕ⟦ CONST n ⟧ σ = n
ℕ⟦ VAR x ⟧ σ = σ x
ℕ⟦ n PLUS m ⟧ σ = ℕ⟦ n ⟧ σ + ℕ⟦ m ⟧ σ
ℕ⟦ n TIMES m ⟧ σ = ℕ⟦ n ⟧ σ * ℕ⟦ m ⟧ σ
ℕ⟦ n MINUS m ⟧ σ = ℕ⟦ n ⟧ σ ∸ ℕ⟦ m ⟧ σ


data Id {A : Set} : A → A → Set where
  id : {x : A} → Id x x


-- R ∪ S = {(x, y) | (x, y) ∈ R v (x, y) ∈ S}
_∪_ : {A : Set} {B : Set}
  → (A → B → Set) 
  → (A → B → Set) 
  ---------------
  → (A → B → Set)
(R ∪ S) x y = R x y ⊎ S x y

-- R ◯ S = {(x, y) | ∃z: (x,z) ∈ R ∧ (z,y) ∈ S}

_◯_ : {A : Set} {B : Set} {C : Set} 
  → (A → B → Set) 
  → (B → C → Set) 
  ---------------
  → (A → C → Set)

(R ◯ S) x y = ∃ λ z → R x z × S z y
  -- it's the same as Σ _ (λ z → R x z × S z y)

-- R ⇃ P = {(x, y) | (x, y) ∈ R ∧ P x}
_⇃_ : {A : Set} {B : Set} 
  → (A → B → Set) 
  → (A → Set) 
  ---------------
  → (A → B → Set)

(R ⇃ P) x y = R x y × P x

denote : Cmd → Σ' → Σ' → Set
denote SKIP = Id
denote (x ::= e) σ σ' = Σ Σ' (λ σ'' → σ'' ≡ σ  × σ' ≡ (σ [ x ↦ ℕ⟦ e ⟧ σ ]))
  -- denote (x ::= e) = {(σ, σ') : σ' ≡ (σ [ x ↦ ℕ⟦ e ⟧ σ ]) }
denote (cmd :: cmd') = (denote cmd) ◯ (denote cmd')
denote WHILE x DO cmd DONE = {!   !}
