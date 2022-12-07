module ADT.Auxiliar where
open import Data.Nat using (ℕ; zero; suc ;_+_; _*_; _∸_;_^_;_⊔_)
open import Data.String using (String)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Bool using (Bool; true; false)

-- Auxiliar data types

--case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
--case x of f = f x

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_ 

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

data List (A : Set) : Set where
  [] : List A
  cons : A → List A → List A

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(cons x xs) ++ ys  =  cons x (xs ++ ys)

[_] : ∀ {A : Set} → A → List A
[ x ] = cons x []




data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x


-- This is for inspecting proofs using with/case.
--    inspect e
--    ... | e1 with≡ eq rewrite eq =  {!  now  eq : e ≡ e1  is in context !}
--    ... | e2 with≡ eq rewrite eq =  {!  now  eq : e ≡ e2 is in context  !}

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl
