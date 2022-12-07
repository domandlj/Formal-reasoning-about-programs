module ADT.Stack.AbstractStack where
open import Data.Maybe.Base
open import Data.Product
  
record IsStack (S A : Set) : Set where
  field
    empty : S
    push :  A → S → S  
    pop : S → Maybe ( S × A )
      
record AbstractStack (A : Set) : Set₁  where 
  field
    Stack : Set
    isStack : IsStack Stack A
  open IsStack isStack public




