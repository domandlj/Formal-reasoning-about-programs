module ADT.Queue.Queue (A : Set) where

open import Data.Nat using (ℕ; zero; suc ;_+_; _*_; _∸_;_^_;_⊔_)
open import Data.String using (String)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Bool using (Bool; true; false)
open import ADT.Auxiliar
open import ADT.Queue.AbstractQueue
open import Function.Base using (case_of_; case_return_of_)

-- implementation

private
  empty' : {A : Set} → List A
  empty' = []
  enqueue' : {A : Set} → A → List A → List A
  enqueue' x q = q ++ [ x ]
  dequeue' : {A : Set} → List A → Maybe ( ( List A ) × A ) 
  dequeue' [] = nothing
  dequeue' ( cons x xs ) = just ( xs , x )
  
  listQueue : {A : Set} → IsQueue (List A) A
  listQueue = record {
          empty = empty' 
        ; enqueue = enqueue'
        ; dequeue = dequeue'
 
      }

  QueueList : AbstractQueue A
  QueueList = record 
    {
      Queue = List A
    ; isQueue = listQueue {A}
    }
    
  -- Public
Queue = AbstractQueue.Queue QueueList  
empty = AbstractQueue.empty QueueList 
enqueue = AbstractQueue.enqueue QueueList
dequeue = AbstractQueue.dequeue QueueList   

  
  
