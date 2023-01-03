module InternaExternalVerif where
import Relation.Binary.PropositionalEquality as Eqq
open import Data.Nat using (ℕ; zero; suc; _+_;_∸_; _*_)
open import Data.Product using (_×_;_,_)
open import Data.List
open import Data.Maybe
open import Data.List.Relation.Unary.Any
open import Data.Bool using (true; false; _∧_; Bool)
open Eqq using (_≡_; refl; cong; cong₂; sym ; trans)
open Eqq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Product

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {x : ℕ}
    
    ----------
    → zero ≤ x

  s≤s : ∀ {x y : ℕ}
    
        → x ≤  y
    --------------------
    → (suc x) ≤ (suc y)

x≤y⇒x≤sy : ∀ {x y : ℕ} 
  
    → x ≤ y 
  ------------
  → x ≤ suc y
x≤y⇒x≤sy z≤n = z≤n
x≤y⇒x≤sy (s≤s r) = s≤s (x≤y⇒x≤sy r)  


record Eq {a} (A : Set a) : Set a where
  field
    _==_ : A → A → Bool

open Eq {{...}} public

natEquals : ℕ → ℕ → Bool
natEquals zero zero = true
natEquals (suc n) (suc m) = natEquals n m
natEquals _  _ = false

instance
  eqList : ∀ {a} {A : Set a} → {{Eq A}} → Eq (List A)
  _==_ {{eqList}} []       []       = true
  _==_ {{eqList}} (x ∷ xs) (y ∷ ys) = x == y ∧ xs == ys
  _==_ {{eqList}} _        _        = false

  eqNat : Eq ℕ
  _==_ {{eqNat}} = natEquals
  
len : {A : Set} → List A → ℕ
len [] = 0
len (x ∷ xs) = 1 + len xs

with-out : ∀ {A : Set} {{eqA : Eq A}} → A → List A → List A
with-out e [] = []
with-out e (x ∷ xs) with e == x
... | true = with-out e xs
... | false = x ∷ with-out e xs


-- prop: len (with-out e xs) ≤ (len xs)
--external verification of a prop
ex-verif : ∀ {A : Set} {{eqA : Eq A}} 

    → (e : A) 
    → (xs : List A) 
    ----------------------------------------
    → (len (with-out e xs)) ≤ (len xs)

ex-verif e [] = z≤n
ex-verif e (x ∷ xs) with e == x
... | true = x≤y⇒x≤sy (ex-verif e xs)
... | false = s≤s (ex-verif e xs)

-- internal verif of a prop
with-out' : ∀ {A : Set} {{eqA : Eq A}} 

  → A 
  → (xs : List A) 
  ------------------------------------------
  → Σ (List A) (λ ys → (len ys) ≤ (len xs))
  
with-out' e [] = ([] , z≤n)
with-out' e (x ∷ xs) with e == x
... | true = ( ys , proof )
  where
    hip = with-out' e xs
    ys = proj₁ hip
    proof = x≤y⇒x≤sy (proj₂ hip)

... | false = (ys , proof)
  where
    hip = with-out' e xs 
    ys =  x ∷ (proj₁ hip)
    proof = s≤s (proj₂ hip)


with-out'≡with-out : ∀ {A : Set} {{eqA : Eq A}}

  → (e : A) 
  → (xs : List A) 
  -----------------------------------------
  → proj₁ (with-out' e xs ) ≡ with-out e xs 
  
with-out'≡with-out e [] = refl
with-out'≡with-out e (x ∷ xs) with e == x
... | true = 
  begin
    proj₁ (with-out' e xs)
  ≡⟨ hip ⟩
    with-out e xs 
  ∎
  where
    hip = with-out'≡with-out e xs

... | false =
  begin
    x ∷ proj₁ (with-out' e xs)
  ≡⟨ cong f hip ⟩
    x ∷ with-out e ( xs)
  ∎
  where
    f = λ xs → x ∷ xs 
    hip = with-out'≡with-out e xs
