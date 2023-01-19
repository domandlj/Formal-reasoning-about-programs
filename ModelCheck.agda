{-# OPTIONS --allow-exec #-}
{-# OPTIONS --guardedness #-}
module ModelCheck where

import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat using (ℕ; zero; suc; _+_;_∸_; _*_)
open import Data.Product using (_×_;_,_)
open import Data.List
open import Data.Maybe
open import Data.List.Relation.Unary.Any
open import Data.Bool
open import TransitionSystem


open Eq using (_≡_; refl; cong; cong₂; sym ; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.Nat.Properties using (+-comm)

--open import SMT.Theories.Nats as Nats
--open import SMT.Backend.Z3 Nats.theory using (solveZ3)

{-

R ∘ S = R(S) = {x | ∃ y ∈ s : yRx }

R^0 = id
R^(n+1) = R ∘ R^n 


For ⟨S, S₀, →⟩ 
Reach(n) = U { →^i(S₀) | i ≤ n } = states reachable after n steps

if for some n Reach(n+1) = Reach(n) then Reach(n) is an invariant 
-}


{-

  OneStepClosureNew : ∀ {State : Set} (sys : TransSys State) (invariant1 invariant2 : State → Set)
            

-}
  

record OneStepClosureCurrent {State} (sys : TransSys State) 
  (invariant1 invariant2 : State → Set) : Set where
  field
    oneStepClosureCurrent : 
              ∀ (s : State) 
            → invariant1 s
            ----------------
            →  invariant2 s

record OneStepClosureNew {State} (sys : TransSys State) 
  (invariant1 invariant2 : State → Set) : Set where
  field
    oneStepClosureNew : 
              ∀ (s s' : State) 
            → invariant1 s
            → (TransSys.step sys) s s'
            ---------------------------
            →  invariant2 s'

record OneStepClosure {State} (sys : TransSys State) 
  (invariant1 invariant2 : State → Set) : Set where
  field
    oneStepClosure : 
                  (OneStepClosureCurrent sys invariant1 invariant2) 
                × (OneStepClosureNew sys invariant1 invariant2)




proveOneStepClosure : ∀ {State} (sys : TransSys State) 
  (invariant1 invariant2 : State → Set)
  
  → (∀ (s  : State) → invariant1 s → invariant2 s)
  → (∀ (s s' : State) → invariant1 s → (TransSys.step sys) s s' → invariant2 s')
  -------------------------------------------------------------------------------
  → OneStepClosure sys invariant1 invariant2

proveOneStepClosure sys inv1 inv2 r1 r2 = record
  { oneStepClosure =
      record { oneStepClosureCurrent = r1 } ,
      record { oneStepClosureNew = r2 }
  }

oneStepClosureDone : ∀ {State} (sys : TransSys State) (invariant : State → Set)
  → (∀ (s : State) → (TransSys.initial sys) s → invariant s)
  → OneStepClosure sys invariant invariant
  -------------------------------------------------------------------------------
  → InvariantFor sys invariant
  
oneStepClosureDone sys inv r1 r2 = h
  where
    h = invariantInduction sys inv r1 (λ s z s' →
      OneStepClosureNew.oneStepClosureNew
      (Data.Product.proj₂ (OneStepClosure.oneStepClosure r2)) s s' z)



data MultiStepClosure : ∀ {State} (sys : TransSys State) 
  (inv inv' : State → Set) → Set₁ where
  mscDone :  ∀ {State} {sys : TransSys State} {inv} 
    
      → OneStepClosure sys inv inv 
      -------------------------------
      → MultiStepClosure sys inv inv
  
  mscStep : ∀ {State} {sys : TransSys State} (inv inv' inv'' : State → Set)
      → OneStepClosure sys inv inv'
      → MultiStepClosure sys inv' inv''
     ---------------------------------
      → MultiStepClosure sys inv inv''







multiStepClosureOk' : ∀ {State} (sys : TransSys State) 
  (inv inv' : State → Set)

  → (MultiStepClosure sys inv inv')
  → (∀ (s : State) → (TransSys.initial sys) s → inv' s)
  ------------------------------------------------------
  → InvariantFor sys inv'

multiStepClosureOk' sys inv .inv (mscDone x) r2 = 
  oneStepClosureDone sys inv r2 (record
 { oneStepClosure =
     record { oneStepClosureCurrent = λ s z → z } ,
     record
     { oneStepClosureNew =
         OneStepClosureNew.oneStepClosureNew
         (Data.Product.proj₂ (OneStepClosure.oneStepClosure x))
     }
 }) 
multiStepClosureOk' sys inv inv' (mscStep .inv inv'' .inv' x r1) r2 = 
  multiStepClosureOk'  sys inv'' inv' r1 r2




multiStepClosureOk : ∀ {State} (sys : TransSys State) (inv : State → Set)

  → (MultiStepClosure sys (TransSys.initial sys) inv)
  ---------------------------------------------------
  → InvariantFor sys inv
  
multiStepClosureOk sys@record { initial = initial ; step = step } .initial m@(mscDone x) = 
  multiStepClosureOk' sys initial initial m λ s z → z
multiStepClosureOk {State} sys@record { initial = initial ; step = step } inv 
  m@(mscStep {sys = sys} .initial i2 .inv record { oneStepClosure = (record { oneStepClosureCurrent = oneStepClosureCurrent } , snd) } multi) = h
  where
    postulate 
      -- perhaps add hoc, but here we define that i2 is the same invariant as inv, the ⇒ case is only needed
      i2⇒inv : ∀  (s : State) → (i2 s) → (inv s)
      inv⇒i2 : ∀  (s : State) →  (inv s) → (i2 s)

    h = multiStepClosureOk' sys initial inv m (λ s i → i2⇒inv s (oneStepClosureCurrent s i))


