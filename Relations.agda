{-# OPTIONS --allow-exec #-}
{-# OPTIONS --guardedness #-}
module Relations where

import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat using (ℕ; zero; suc; _+_;_∸_)


open Eq using (_≡_; refl; cong; cong₂; sym ; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.Nat.Properties using (+-comm)

open import SMT.Theories.Nats as Nats
open import SMT.Backend.Z3 Nats.theory using (solveZ3)

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


data < : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → < zero (suc n)

  s<s : ∀ {m n : ℕ}
    → < m n
      -------------
    → < (suc m) (suc n)





<-trans : ∀ {x y z : ℕ}
  
  → < x y       → < y z 
  ---------------------
        → < x z
<-trans z<s (s<s n<m) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)



<xsx : ∀ {x : ℕ}

  ---------------------
    → < x (suc x)
<xsx {zero} = z<s
<xsx {suc x} = s<s <xsx


≺' : ℕ → ℕ → Set
≺' x y = ^ ≺ x y



≺⊆< : ∀ (x y : ℕ) 
  
      → ≺ x y
  -------------------
      → < x y
≺⊆< x y (≺-cons r)
  rewrite (sym r) = <xsx


≺'⊆< : ∀ (x y : ℕ) 
  
      → ≺' x y
  -------------------
      → < x y


≺'⊆< x y (^-base r) = ≺⊆< x y r
≺'⊆< x y (^-trans {x = x}  {y = z} {z = y} r1 r2) = <-trans h1 h2
  where
    h1 : < x z
    h1 = ≺'⊆< x z r1

    h2 : < z y
    h2 = ≺'⊆< z y r2

x≺'1+k+x : ∀ (x k : ℕ) 

  ----------------------
    → ≺' x (1 + k + x)

x≺'1+k+x x zero = ^-base (≺-cons refl)
x≺'1+k+x x (suc k) = ^-trans (x≺'1+k+x x k) (^-base (≺-cons refl))

-- Z3 help!
arith-1 : ∀ {x y : ℕ} → (1 +  (y ∸ x ∸ 1) + x) ≡ y 
arith-1 = solveZ3

<⊆≺' : ∀ (x y : ℕ) 
  
      → < x y
  -------------------
      → ≺' x y
<⊆≺' x y _ = part2
  where

    part1 : (≺' x (1 +  (y ∸ x ∸ 1) + x) ) ≡ (≺' x y) 
    part1 =
      begin
        ≺' x (1 +  (y ∸ x ∸ 1) + x)
      ≡⟨ cong₂ ≺' refl (arith-1 {x} {y}) ⟩
        ≺' x y
      ∎
    
    part2 : ≺' x y
    part2 
      rewrite (sym part1) = x≺'1+k+x x (y ∸ x ∸ 1)

  



