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

    →  x + 1 ≡ y
    -------------
    →  ≺ x y

≺-inv : ∀ (x y : ℕ) 
  → ≺ x y 
  → x + 1 ≡ y

≺-inv x y (≺-cons x+1≡y) = x+1≡y


data ≤ : ℕ → ℕ → Set where

  z≤n : ∀ {x : ℕ}
    
    ----------
    → ≤ zero x

  s≤s : ∀ {x y : ℕ}
    
        → ≤ x  y
    --------------------
    → ≤ (suc x) (suc y)




< : ℕ → ℕ → Set
< x y = ≤ (suc x)  y

≺' : ℕ → ℕ → Set
≺' x y = ^ ≺ x y

prop1 : ∀ (x y : ℕ) 
  
      → ≺' x y
  -------------------
      → < x y

prop1 zero y ≺'zy = {!  !}
prop1 (suc x) y ≺'sy = {!   !}