{-# OPTIONS --allow-exec #-}
{-# OPTIONS --guardedness #-}
module TransSystem where

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

{-
factorial(n) {
  a = 1;
  while (n > 0) {
    a = a * n;
    n = n - 1;
  }
  
  return a; 
}
-}


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



 
postulate
  invariantInduction :  ∀ {State : Set} (sys : TransSys State) (invariant : State → Set)

    → ( ∀ (s : State) →  (TransSys.initial sys) s →  invariant s)
    → (∀ (s : State) → invariant s → ∀ (s' : State) →  (TransSys.step sys) s s' → invariant s')
    --------------------------------------------------------------------------------------------------
           → InvariantFor sys invariant
  -- this can be proved.
  




-- arithmetic
n*1≡n :  ∀ (n : ℕ) → n * 1 ≡ n
n*1≡n zero = refl
n*1≡n (suc n) = begin
    suc (n * 1)
  ≡⟨ cong suc (n*1≡n n) ⟩
    suc n 
  ∎

n+0≡n : ∀ (n : ℕ) → n + 0 ≡ n
n+0≡n zero = refl
n+0≡n (suc n) = begin
    suc (n + 0)
  ≡⟨ cong suc (n+0≡n n) ⟩
    suc n
  ∎

m≡n+0⇒m≡n : ∀ {m n : ℕ} 
    → m ≡ (n + zero)
    → m ≡ n
m≡n+0⇒m≡n {m} {n} m≡n+0 = 
  begin
    m
  ≡⟨ m≡n+0 ⟩
    n + 0
  ≡⟨ n+0≡n n ⟩
    n
  ∎


postulate
  identity1 : ∀ (m a : ℕ) →  (m !) * (a * (m + 1)) ≡ ((m + 1) !) * a


invariantFactorial : ℕ → FactState → Set
invariantFactorial n (return x) = n ! ≡ x
invariantFactorial n (acc x a) = n ! ≡ x ! * a


invariantFactorialCorrect : ∀ (n : ℕ) →   
  
  ---------------------------------------------------------
    InvariantFor (factorialSys n) (invariantFactorial n)
    
invariantFactorialCorrect n = 
  invariantInduction (factorialSys n) (invariantFactorial n) baseCase inductiveCase
  where
    baseCase : ∀ (s : FactState) → FactInit n s → invariantFactorial n s
    baseCase (acc x .1) factInit
      rewrite  n*1≡n (x !)  = refl
    
    inv-trans : ∀ (n : ℕ) ( s s' : FactState)
        
        → invariantFactorial n s
        → ⊳ s s'
        ---------------------------
         →  invariantFactorial n s'
 
    inv-trans n .(acc 0 _) .(return _) invFact factDone 
      rewrite m≡n+0⇒m≡n invFact = refl
    inv-trans n .(acc (m + 1) a) .(acc m (a * (m + 1))) invFact (factStep m a)
      rewrite identity1 m a
        | invFact = refl
    
    inductiveCase : ∀  (s : FactState) 

            → invariantFactorial n s 
            → ∀ (s' : FactState) 
            → TransSys.step (factorialSys n) s s'
            --------------------------------------
            → invariantFactorial n s'
            
    inductiveCase s invFact s' step  = inv-trans n s s' invFact step

invariantFactorialAlways :  ∀ (n : ℕ) (s : FactState) 

    →  Reachable (factorialSys n) s
    ----------------------------------------------
    →  invariantFactorial n s 

invariantFactorialAlways n s reach = 
  useInvariant (factorialSys n) (invariantFactorial n) s (invariantFactorialCorrect n) reach

factOk' : ∀ (n : ℕ) (s : FactState) →

  FactFinal s
  → invariantFactorial n s
  ------------------------
  → s ≡ return ( n !)
  
factOk' n .(return a) (factFinal a) inv
   rewrite sym inv = refl

factOk : ∀ (n : ℕ) (s : FactState) 

  → Reachable (factorialSys n) s
  → FactFinal s
  -------------------------------
  → s ≡ return ( n !)
factOk n s reach final = factOk' n s final always
  where
    always = invariantFactorialAlways n s reach



{-
      PART 2. CONCURRENT PROGRAM 
-}

{-
  lock();
  local := global;
  global := local + 1;
  unlock();
-}

data IncrementProgram : Set where
  lock : IncrementProgram
  read : IncrementProgram
  write : ℕ → IncrementProgram
  unlock : IncrementProgram
  done : IncrementProgram


-- shared state
record IncState : Set where
  field
    locked : Bool
    global : ℕ

record ThreadedState (Shared Priv : Set) : Set  where
  field
    shared : Shared
    priv : Priv


IncrementState : Set
IncrementState = ThreadedState IncState IncrementProgram

data IncrementInit : IncrementState → Set where
  incInit : IncrementInit (
    record {   
      shared = record { 
          locked = false 
        ; global = 0 
        }
      ; priv = lock
      }
    )

data IncrementStep : IncrementState → IncrementState → Set where
  incLock : ∀ (g : ℕ) → 
    IncrementStep 
      (record
      {   shared = record { locked = false ; global = g } 
        ; priv = lock 
      }) 
      
      (record
      {   shared = record { locked = true ; global = g } 
        ; priv = read 
      })

  incRead : ∀ (l : Bool) (g : ℕ) → 
    IncrementStep 
      (record
      {   shared = record { locked = l ; global = g } 
        ; priv = read }) 
      
      (record
      {   shared = record { locked = l ; global = g } 
        ; priv = write g 
      })

  incWrite : ∀ (l : Bool) (g n : ℕ) → 
    IncrementStep 
      (record
      {   shared = record { locked = l ; global = g } 
        ; priv = write n }) 
      
      (record
      {   shared = record { locked = l ; global = (suc n) } 
        ; priv = unlock 
      })

  incUnlock : ∀ (l : Bool) (g : ℕ) → 
    IncrementStep 
      (record
      {   shared = record { locked = l ; global = g } 
        ; priv = unlock }) 
      
      (record
      {   shared = record { locked = l ; global = g } 
        ; priv = done 
      })


IncrementSys : TransSys IncrementState
IncrementSys = record 
  {
      initial = IncrementInit
    ; step = IncrementStep
  }

-- IncrementSys is a transition sys in a single thread

-- Two threads


data ParallelInit {Shared Priv1 Priv2 : Set} 
    (Init1 : (ThreadedState Shared Priv1) → Set)
    (Init2 : (ThreadedState Shared Priv2) → Set)  
      : ThreadedState Shared (Priv1 × Priv2) → Set  where
  
  p-init : ∀ (sh : Shared) (pr1 : Priv1) (pr2 : Priv2) 

    → Init1 (record { shared = sh ; priv = pr1 }) 
    → Init2 (record { shared = sh ; priv = pr2 }) 
    -----------------------------------------------------------------------
    → ParallelInit Init1 Init2 (record { shared = sh ; priv = (pr1 , pr2) })


data ParallelStep {Shared Priv1 Priv2 : Set}  
    (Step1 : (ThreadedState Shared Priv1) → (ThreadedState Shared Priv1) → Set)
    (Step2 : (ThreadedState Shared Priv2) → (ThreadedState Shared Priv2) → Set)  
    : (ThreadedState Shared (Priv1 × Priv2)) → (ThreadedState Shared (Priv1 × Priv2)) → Set  where

  -- fst thread runs
  p-step1 : ∀ (sh sh' : Shared) (pr1 pr1' : Priv1) (pr2 : Priv2)

    
    → Step1 (record { shared = sh ; priv = pr1 }) (record { shared = sh' ; priv = pr1' })
    -------------------------------------------------------------------------------------
    → ParallelStep Step1 Step2
          (record { shared = sh ; priv = (pr1 , pr2) })
          (record { shared = sh' ; priv = (pr1' , pr2) })
  
  -- snd thread runs        
  p-step2 : ∀ (sh sh' : Shared) (pr1 : Priv1) (pr2 pr2' : Priv2)

    
    → Step2 (record { shared = sh ; priv = pr2 }) (record { shared = sh' ; priv = pr2' })
    -------------------------------------------------------------------------------------
    → ParallelStep Step1 Step2
          (record { shared = sh ; priv = (pr1 , pr2) })
          (record { shared = sh' ; priv = (pr1 , pr2') })


Parallel : {Shared : Set} → {Priv1 : Set} → {Priv2 : Set} 
    → TransSys (ThreadedState Shared Priv1) 
    → TransSys (ThreadedState Shared Priv2)
    --------------------------------------------------
    → TransSys (ThreadedState Shared (Priv1 × Priv2))  
    
Parallel Sys1 Sys2 = record 
  {
    initial = ParallelInit ((TransSys.initial) Sys1) ((TransSys.initial) Sys2)
    ; step = ParallelStep ((TransSys.step) Sys1) ((TransSys.step) Sys2)
  }

Increment2Sys = Parallel IncrementSys IncrementSys


-- invariant
data Increment2Invariant : ThreadedState IncState (IncrementProgram × IncrementProgram) → Set where

  inct2inv :  ∀ {sh : IncState } {pr1 pr2 : IncrementProgram}
  
    --------------------------------------------------------------------
    → Increment2Invariant (record { shared = sh  ; priv = pr1 , pr2 })



Increment2InvariantOk : InvariantFor Increment2Sys Increment2Invariant
Increment2InvariantOk = invariantInduction (record
      { initial = ParallelInit IncrementInit IncrementInit
          ; step = ParallelStep IncrementStep IncrementStep
      }) Increment2Invariant baseCase inductiveCase 
  where

    baseCase : ∀ (s : ThreadedState IncState (IncrementProgram × IncrementProgram)) 
            → ParallelInit IncrementInit IncrementInit s 
            → Increment2Invariant s
    baseCase .(record { shared = sh ; priv = pr1 , pr2 }) (p-init sh pr1 pr2 x x₁) = inct2inv

    
    inductiveCase : ∀ (s : ThreadedState IncState (IncrementProgram × IncrementProgram)) 
      → Increment2Invariant s 
      → ∀ (s' : ThreadedState IncState (IncrementProgram × IncrementProgram)) 
      → ParallelStep IncrementStep IncrementStep s s' 
      →  Increment2Invariant s'
    inductiveCase .(record { shared = _ ; priv = _ , _ }) 
      inct2inv .(record { shared = sh' ; priv = pr1' , _ }) (p-step1 _ sh' _ pr1' _ x) = inct2inv
    inductiveCase .(record { shared = _ ; priv = _ , _ }) 
      inct2inv .(record { shared = sh' ; priv = _ , pr2' }) (p-step2 _ sh' _ _ pr2' x) = inct2inv


-- when one invariant implies another ? 

InvariantWeaken : ∀ {State} (sys : TransSys State) (invariant1 invariant2 : State → Set)
  
  → InvariantFor sys invariant1
  →  (∀ (s : State) → invariant1 s → invariant2 s)
  ------------------------------------------------
  → InvariantFor sys invariant2 

InvariantWeaken sys invariant1 invariant2 z _ =
  record
  { invariantFor =
      λ sys₁ invariant s → InvariantFor.invariantFor z sys₁ (λ _ → invariant s) s
  }




-- Increment2InvariantOk : InvariantFor Increment2Sys Increment2Invariant

-- Weaker invariant corresponding exactly to the overall correctness property we want to establish for this system
{-
Increment2RightAnswer : ThreadedState IncState (IncrementProgram × IncrementProgram) → Set 
Increment2RightAnswer s =  
  
    (ThreadedState.priv s) ≡ (done , done) 
  -------------------------------------------------
  → (IncState.global (ThreadedState.shared s)) ≡ 2

Increment2RightAnswerInv : InvariantFor Increment2Sys Increment2RightAnswer
Increment2RightAnswerInv = InvariantWeaken (record
      { initial = ParallelInit IncrementInit IncrementInit
        ; step = ParallelStep IncrementStep IncrementStep
      }) Increment2Invariant Increment2RightAnswer Increment2InvariantOk ?


Increment2SysCorrect : ∀ {s} → Reachable Increment2Sys s → Increment2RightAnswer s
Increment2SysCorrect s reach =  ?  
-}




    
    

  