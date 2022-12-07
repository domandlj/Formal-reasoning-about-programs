module ADT.Stack.Stack (A : Set) where

open import ADT.Stack.AbstractStack
open import Data.Maybe.Base
open import Data.List.Base
open import Data.Product
open import Data.Nat using (ℕ; _+_; _*_;_∸_) 
 


  -- implementation
private 
  empty' : {A : Set} → List A
  empty' = []

  push' : {A : Set} → A → List A → List A
  push' x s = x ∷ s

  pop' : {A : Set} → List A → Maybe ( ( List A ) × A ) 
  pop' [] = nothing
  pop' ( x ∷ xs ) = just ( xs , x )

    
  listStack : {A : Set} → IsStack (List A) A
  listStack = record {
          empty = empty' 
        ; push = push'
        ; pop = pop'
      }

  
  StackList : AbstractStack A
  StackList = record {
        Stack = List A
      ; isStack = listStack {A}
      }
    
-- public interface
Stack = AbstractStack.Stack StackList  
empty = AbstractStack.empty StackList 
push = AbstractStack.push StackList 
pop = AbstractStack.pop StackList

  
  

  