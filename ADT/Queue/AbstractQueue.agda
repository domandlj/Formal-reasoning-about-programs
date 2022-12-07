module ADT.Queue.AbstractQueue where

open import Data.Nat using (ℕ; zero; suc ;_+_; _*_; _∸_;_^_;_⊔_)
open import Data.String using (String)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Bool using (Bool; true; false)
open import ADT.Auxiliar
open import Function.Base using (case_of_; case_return_of_)




record IsQueue (Q A : Set) : Set where
  field
    empty : Q 
    enqueue :  A → Q → Q 
    dequeue : Q → Maybe ( Q × A )

  postulate
    queue-spec-1 : dequeue empty ≡ nothing
    queue-spec-2 : ∀ {A : Set} {q : Q}  

      →  dequeue q ≡ nothing 
    ------------------------
      → q ≡ empty

    queue-spec-3 : ∀ {x : A} {q : Q} 

      -----------------------------------------------------------  
      → dequeue (enqueue x q) ≡  just ( 
        case (dequeue q) of λ where
          nothing            → ( empty , x )
          (just ( q' , y ) ) → ( enqueue x q' , y )  
        )
  
  

record AbstractQueue (A : Set) : Set₁  where 
  field
    Queue : Set
    isQueue : IsQueue Queue A
  open IsQueue isQueue public




{-
Alternative  ADT existential types with Σ
 
record Σ  (A : Set₁ ) (B : A → Set₀) : Set₁  where
  constructor _,_
  field
    proj₁  : A
    proj₂  : B proj₁

AbstractStack : Set → Set₁ 
AbstractStack A = Σ Set (λ S → IsStack S A)

StackN : AbstractStack ℕ
StackN = ( List ℕ , listStack {ℕ})

b : Σ.proj₁ StackN
b = (IsStack.push (Σ.proj₂ StackN)) 1 (IsStack.nil (Σ.proj₂ StackN))
-} 