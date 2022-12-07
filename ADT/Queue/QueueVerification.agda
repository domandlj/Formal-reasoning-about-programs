module ADT.Queue.QueueVerification where

open import Data.Nat using (ℕ; zero; suc ;_+_; _*_; _∸_;_^_;_⊔_)
open import Data.String using (String)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Bool using (Bool; true; false)
open import ADT.Auxiliar
open import ADT.Queue.Queue
open import Function.Base using (case_of_; case_return_of_)

queue-spec-1 : {A : Set} → (dequeue A) (empty A) ≡ nothing
queue-spec-2 : ∀ {A : Set} {q : Queue A}  
    
      →  (dequeue A) q ≡ nothing 
    ----------------------------
      → q ≡ (empty A)

queue-spec-3 : ∀ {A : Set} {x : A} {q : Queue A} 
  
    -----------------------------------------------------------  
    → (dequeue A) (enqueue A x q) ≡ just ( 
        case (dequeue A q) of λ where
            nothing            → ( empty A , x )
            (just ( q' , y ) ) → ( enqueue A x q' , y )  
      )

queue-spec-1 = refl
queue-spec-2 {A} {[]} r = refl

queue-spec-3 {A} {x} {[]} with (dequeue A [])
... | nothing  =  refl 
... | just _ = refl
queue-spec-3 {A} {x} {cons x' q'}  with inspect (dequeue A (cons x' q'))
... | ( nothing ) with≡ eq rewrite eq | queue-spec-2 eq = refl
... | ( just (q''' , y) ) with≡ eq rewrite eq  | (queue-spec-2 {A} queue-spec-1 ) = refl