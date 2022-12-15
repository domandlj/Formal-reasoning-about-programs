module Relations where

import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat using (ℕ; zero; suc; _+_)


open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.Nat.Properties using (+-comm)

-- relations 
-- reflex:         ∀ x     . xRx
-- simmetric:      ∀ x y   . xRy ⇒ yRx
-- antisimmetric:  ∀ x y   . xRy ∧ yRx ⇒  x ≡ y
-- transistive:    ∀ x y z . xRy ∧ yRz ⇒  xRz 
-- total:          ∀ x y   . xRy v yRx 
-- 
-- A relation R is
-- Preorder: reflexive and transitive.
-- Partial order: preorder and antisimmetric.
-- Total order: partial order and total


data ^ : ∀ {A : Set} (R : A → A → Set) → A → A → Set where
  ^-base : ∀ {A} {R : A → A → Set } {x y} 

    →  R x y
    ------------
    → ^ R x y

  ^-trans : ∀ {A} {R : A → A → Set} {x y z}

    →  ^ R x y              → ^ R y z
    ----------------------------------
               → ^ R x z           


data ≺ : ℕ → ℕ → Set where
  ≺-cons : ∀ {x y : ℕ} 

    →  suc x ≡ y
    -------------
    →  ≺ x y

≺-inv : ∀ (x y : ℕ) 
  → ≺ x y 
  → suc x ≡ y

≺-inv x y (≺-cons x+1≡y) = x+1≡y


data ≤ : ℕ → ℕ → Set where

  z≤n : ∀ {x : ℕ}
    
    ----------
    → ≤ zero x

  s≤s : ∀ {x y : ℕ}
    
        → ≤ x  y
    --------------------
    → ≤ (suc x) (suc y)

x≤x : ∀ (x : ℕ) → ≤ x x
x≤x zero = z≤n
x≤x (suc x) = s≤s (x≤x x)



< : ℕ → ℕ → Set
< x y = ≤ (suc x)  y



≺' : ℕ → ℕ → Set
≺' x y = ^ ≺ x y


≺⊆< : ∀ (x y : ℕ) 
  
      → ≺ x y
  -------------------
      → < x y
≺⊆< x y (≺-cons r)
  rewrite (sym r) = x≤x (suc x)

≺'⊆< : ∀ (x y : ℕ) 
  
      → ≺' x y
  -------------------
      → < x y

≺'⊆< x y (^-base r) = ≺⊆< x y r
≺'⊆< x y (^-trans {x = x}  {y = z} {z = y} r1 r2) = <-trans' x z y h1 h2
  where
    h1 : < x z
    h1 = ≺'⊆< x z r1

    h2 : < z y
    h2 = ≺'⊆< z y r2
    postulate
      <-trans' : ∀ (a b c : ℕ) → < a b → < b c → < a c

 