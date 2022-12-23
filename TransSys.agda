{-# OPTIONS --allow-exec #-}
{-# OPTIONS --guardedness #-}
module TransSys where

import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat using (ℕ; zero; suc; _+_;_∸_; _*_)
open import Data.Product using (_×_;_,_)
open import Data.List
open import Data.Maybe
open import Data.List.Relation.Unary.Any
open import Data.Bool


open Eq using (_≡_; refl; cong; cong₂; sym ; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.Nat.Properties using (+-comm)

--open import SMT.Theories.Nats as Nats
--open import SMT.Backend.Z3 Nats.theory using (solveZ3)


_! : ℕ → ℕ
zero ! = suc zero
(suc n) ! = (suc n) * n !

data FactState : Set where
  return : ℕ → FactState
  acc : ℕ → ℕ → FactState

data FactInit (n₀ : ℕ) : FactState → Set where
  factInit : 
  
    ----------------------
    FactInit n₀ (acc n₀ 1)

data FactFinal : FactState → Set where
  factFinal : ∀ (a : ℕ) → 
  
    --------------------
    FactFinal (return a)

-- ⊳ is the transition relation of the factorial state machine
data ⊳ : FactState → FactState → Set where
  factDone :  ∀ {a : ℕ} → 
    
    ----------------------------
      ⊳ (acc 0 a) (return a)
  
  factStep : ∀ (n a : ℕ) →

    --------------------------------------------
      ⊳ (acc (n + 1) a)  (acc n (a * (n + 1)))

    

-- Transitive reflexive clousure of a relation.

data ✷ : ∀ {A : Set} (R : A → A → Set) → A → A → Set where
  ✷-refl : ∀ {A} {R : A → A → Set} {x} 

    ------------
    → ✷ R x x

  ✷-trans : ∀ {A} {R : A → A → Set} {x y z}

    → R x y              → ✷ R y z
    ----------------------------------
               → ✷ R x z          

✷-id :  ∀ {A : Set} (R : A → A → Set) (x y : A)
  
    →  R x y
  ------------
    → ✷ R x y

✷-id R x y Rxy = ✷-trans Rxy ✷-refl    

✷-is-trans : ∀ {A : Set} {R : A → A → Set} {x y z : A}

  → ✷ R x y              → ✷ R y z
  ----------------------------------------------
      →  ✷ R x z

✷-is-trans ✷-refl ✷Ryz = ✷Ryz
✷-is-trans (✷-trans x t) ✷Ryz = ✷-trans x (✷-is-trans t ✷Ryz)

-- Example factorial of 3 is 6

factorial3 : ✷ ⊳ (acc 3 1) (return 6)
factorial3 =  ✷-trans (factStep 2 1) (✷-trans (factStep 1 3) (
              ✷-trans (factStep zero 6) (✷-trans factDone ✷-refl)
            ))



record TransSys (State : Set) : Set₁  where
  field
    initial : State → Set 
    step : State → State → Set


factorialSys : ∀ (n₀ : ℕ) → TransSys FactState
factorialSys n₀ = record 
  {
      initial = FactInit n₀ 
    ; step = ⊳
  }



-- For a ts ⟨S, S₀, →⟩ Reachable = {s ∈ S | s₀ ∈ S₀  ∧ s₀ →✷ s }
data Reachable : ∀ {State : Set} → (sys : TransSys State) → (s : State) → Set₁ where

  reachable : ∀ {State} {sys : TransSys State} {s₀ s : State}
  
      → (TransSys.initial sys) s₀               → ✷ (TransSys.step sys) s₀ s
      --------------------------------------------------------------------------
        →  Reachable sys s

-- For a ts ⟨S, S₀, →⟩, I ⊆ S is an invariant if Reachable ⊆ I
-- In a ts a state s satisfies a propertie P, P s if s ∈ P
-- ∀ s : Reachable s ⇒ I s



record InvariantFor {State : Set} (sys : TransSys State) (invariant : State → Set) : Set₁  where
  field
    invariantFor : ∀ {State : Set} (sys : TransSys State) (invariant : State → Set) 
  
      → ∀ (s : State) → (TransSys.initial sys) s        
      → ∀ (s' : State) → ✷ (TransSys.step sys) s s'
      ----------------------------------------------
          → invariant s


useInvariant' : ∀ {State : Set} (sys : TransSys State) (invariant : State → Set) (s s' : State)

    → InvariantFor sys invariant       
    → (TransSys.initial sys) s        
    → ✷ (TransSys.step sys) s s'
    ------------------------------
          → invariant s' 

useInvariant' = λ sys invariant s s' z z₁ →
  InvariantFor.invariantFor z sys (λ _ → invariant s') s z₁ s'


useInvariant : ∀ {State : Set} (sys : TransSys State) (invariant : State → Set) (s : State)

    → InvariantFor sys invariant       
    → Reachable sys s        
    ------------------------------
      → invariant s 

useInvariant sys invariant s inv (reachable {s₀ = s₀} {s = s} init step) = 
  useInvariant' sys invariant s₀ s inv init step


fact-inv : ℕ → FactState → Set
fact-inv n (return x) = n ! ≡ x
fact-inv n (acc x a) = n ! ≡ x ! * a

