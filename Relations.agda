{-# OPTIONS --allow-exec #-}
{-# OPTIONS --guardedness #-}
module Relations where

import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat using (ℕ; zero; suc; _+_;_∸_)
open import Data.Product using (_×_;_,_)
open import Data.List
open import Data.Maybe
open import Data.List.Relation.Unary.Any
open import Data.Bool


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

postulate 
  -- this axioms makes sense, (p ⇒ q) ∧ (q ⇒ p)  is p ≡ q 
  relation-≡ : ∀ {A B : Set} {r1 r2 : A → B → Set} {x : A} {y : B}
  
    → (r1 x y → r2 x y) × (r2 x y → r1 x y)
    -----------------------------------------------
    → r1 x y ≡ r2 x y

≺'≡< : ∀ (x y : ℕ)

    --------------------
    → (≺' x y ≡ < x y)
≺'≡< x y = 
  relation-≡ 
    {r1 = ≺'} {r2 = <} 
    ( ≺'⊆< x y , <⊆≺' x y )


-- 𝜋
-- permutations of list
data π {A : Set} : List A → List A → Set where
  π-empty : 
    
    ------------
      π [] [] 
  
  π-add : ∀ {xs ys : List A} {x : A} 
    
    → π xs ys
   ------------------------
    → π (x ∷ xs) ( x ∷ ys)
  
  π-add2 : ∀ {xs : List A} {x y : A}

    ---------------------------------
     → π (x ∷ y ∷ xs) ( y ∷ x ∷ xs)
  
  π-trans : ∀ {xs ys zs : List A}
  
    → π xs ys                     → π ys zs
    ---------------------------------------
          → π xs zs

-- example

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)

li1 : List ℕ
li1 = 2 ∷ 3 ∷ 10 ∷ 0 ∷ []

li2 : List ℕ
li2 = 10 ∷ 2 ∷ 3 ∷ 0 ∷ []

perm : π li1 li2
perm = π-trans (π-add π-add2) π-add2


-- relation min x xs when x is the min of xs
data min  : ℕ → List ℕ → Set where
  [] : ∀ {x} →

   ----------
    min x []
    
  _∷_ : ∀ {x y} {ys} 
    
    → ≤ x y           → min x ys 
    -------------------------------
       → min x (y ∷ ys)

-- Proof that a list in ascending order
data InOrder : List ℕ → Set where
  []  : InOrder []
  _∷_ : ∀ {x xs} 
    
    → min x xs                → InOrder xs 
    --------------------------------------
      → InOrder (x ∷ xs)

record Sorted (xs : List ℕ) : Set where
  field
    ys       : List ℕ
    inOrder  : InOrder ys
    isPerm   : π ys xs



-- Skeleton for proving that a sorting function is correct
postulate
  dumb-sort : List ℕ → List ℕ
  dumb-order : ∀ {xs : List ℕ} → InOrder (dumb-sort xs)
  dumb-perm :  ∀ {xs : List ℕ} → π (dumb-sort xs) xs

correct-dumb-sort : ∀ (xs : List ℕ) → Sorted xs 
correct-dumb-sort xs = record 
  {
      ys = dumb-sort xs
    ; inOrder = dumb-order
    ; isPerm = dumb-perm
  }
