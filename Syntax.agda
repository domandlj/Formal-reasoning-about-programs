
module Syntax where

open import Data.Nat using (ℕ; zero; suc ;_+_; _*_; _∸_;_^_;_⊔_)
open import Data.String using (String)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Bool using (Bool; true; false)


{-
    e ::= n ‖ x ‖ e + e ‖ e × e         (Exp)
    n ::= ℕ                             (const)
    x ::= String                        (var)
-}

data Exp : Set where
    const : ℕ → Exp
    var : String → Exp
    _×'_ : Exp → Exp → Exp
    _+'_ : Exp → Exp → Exp

infix 5 _×'_
infix 4 _+'_

-- Examples of expressions

-- (0 + 1) × z
exp1 = (const 0 +' const 1) ×' var "z" 

‖_‖ : Exp → ℕ
‖ const x ‖  = 1
‖ var x ‖ = 1
‖ e ×' e' ‖ = 1 + ‖ e ‖ + ‖ e' ‖
‖ e +' e' ‖ = 1 + ‖ e ‖ + ‖ e' ‖


infix 4 _≤_
data _≤_ : ℕ → ℕ → Set where

  ≤-zero : ∀ {x : ℕ}

    ------------
    → zero ≤ x

  ≤-suc : ∀ {x y : ℕ}

        → x ≤ y
    ----------------
    → suc x ≤ suc y

≤-refl : ∀ {n : ℕ}

  --------
  → n ≤ n
≤-refl {zero} = ≤-zero
≤-refl {suc n} = ≤-suc ≤-refl


≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans ≤-zero _ =  ≤-zero
≤-trans (≤-suc m≤n) (≤-suc n≤p) = ≤-suc (≤-trans m≤n n≤p)

depth : Exp → ℕ
depth (const x) = 1
depth (var x) = 1
depth (e ×' e') = depth e ⊔ depth e'
depth (e +' e') = depth e ⊔ depth e'



postulate
  lemma-1 : ∀ {a b a' b' : ℕ}  
    
    → (a ≤ a')          → (b ≤ b')     
    -------------------------------
        →  a ⊔ b ≤ suc ( a' + b' )
  
  +-zero : ∀ (x : ℕ) → zero + x ≡ x
  ⊔-zero : ∀ (x : ℕ) → zero ⊔ x ≡ x
  ⊔-suc : ∀ (x y : ℕ) → (suc x ) ⊔ y ≡ suc (x ⊔ y)
  suc-mono : ∀ (x y : ℕ)
      → x ≤ y
    ----------------
      → (suc x) ≤ (suc y)
  
  

prop : ∀ (a b : ℕ) →  (a ⊔ b) ≤ (a + b)
prop zero b 
  rewrite (⊔-zero (zero ⊔ b)) 
        | (+-zero (zero + b)) = ≤-refl

prop (suc a) b 
  rewrite (⊔-suc a  b) = suc-mono (a ⊔ b) (a + b) (prop a b)





-- theorem
theorem-1 : ∀ (e : Exp ) → depth e ≤ ‖ e ‖
theorem-1 (const x) = ≤-suc ≤-zero
theorem-1 (var x) = ≤-suc ≤-zero
theorem-1 (e ×' e') = lemma-1 (theorem-1 e) (theorem-1 e')
theorem-1 (e +' e') = lemma-1 (theorem-1 e) (theorem-1 e')




{-

  AUTOMATION EXAMPLE
  (reflection)

-}

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where
  -- nothing 
  
data Even : ℕ → Set where
  isEven0 : Even 0
  isEven+2 : {n : ℕ} → Even n → Even (2 + n)

even? : ℕ → Set
even? 0 = ⊤
even? 1 = ⊥
even? (suc (suc n)) = even? n



soundnessEven : {n : ℕ} → even? n → Even n
soundnessEven {0} tt = isEven0
soundnessEven {1} ()
soundnessEven {suc (suc n)} s = isEven+2 (soundnessEven s)

isEven8772 : Even 8772
isEven8772 = soundnessEven tt

isEven4 : Even 4
isEven4 = soundnessEven tt