module Denotational where
import Relation.Binary.PropositionalEquality as Eqq
open import Data.Nat using (ℕ; zero; suc; _+_;_∸_; _*_)
open import Data.Product using (_×_;_,_)
open import Data.List
open import Data.Maybe
open import Function.Base using (flip)
open import Data.List.Relation.Unary.Any
open import Data.Bool using (true; false; _∧_; Bool; if_then_else_)
open Eqq using (_≡_; refl; cong; cong₂; sym ; trans)
open Eqq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Product
open import Data.String using (String; _≟_)
open import Relation.Nullary using (yes; no)
open import Data.Sum.Base
open import Level using (Level; _⊔_) renaming (suc to succ)

{--
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



data _≤ᶠ_ : (ℕ → ℕ) → (ℕ → ℕ) → Set where
  ≤ᶠ-rule : ∀ {x : ℕ} {f g : (ℕ → ℕ)}

    → f x ≤ g x
    ----------------
    → f ≤ᶠ g

infix 4 _≤ᶠ_
--}

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

-- In set theory:  for a set A and P a predicate over A (i.e. P ⊆ A), S = {x ∈ A | P x }
-- In type theory: A : Set, P : A → Set and  S = Σ A P  


-- {n : ℕ | 4 ≤ n}, here ℕ is the set and less than four the predicate.

--m : Σ ℕ (λ n → 4 ≤ n)
--m = 5 , s≤s (s≤s (s≤s (s≤s z≤n)))

Var = String
Σ' = Var → ℕ

data Boolean : Set where
  TRUE : Boolean
  FALSE : Boolean


data Arith : Set where
  CONST : ℕ → Arith
  VAR : Var → Arith
  _PLUS_ : Arith → Arith → Arith
  _TIMES_ : Arith → Arith → Arith
  _MINUS_ : Arith → Arith → Arith


data Cmd : Set where 
  SKIP   : Cmd
  _::=_ : Var → Arith → Cmd
  _::_ : Cmd → Cmd → Cmd
  WHILE_DO_DONE : Boolean → Cmd → Cmd

_[_/_] : Arith → Arith → Var → Arith
CONST n [ e / x ] = CONST n
VAR y [ e / x ] with y ≟ x
... | yes _ = e
... | no  _ = VAR y
(n PLUS m) [ e / x ] =  (n [ e / x ]) PLUS (m [ e / x ])
(n TIMES m) [ e / x ] =  (n [ e / x ]) TIMES (m [ e / x ])
(n MINUS m) [ e / x ] =  (n [ e / x ]) MINUS (m [ e / x ])


_[_↦_] : Σ' → Var → ℕ → Σ'
(σ [ X ↦ n ]) Y with Y ≟ X
... | yes _ = n
... | no  _ = σ Y

ℕ⟦_⟧ : Arith → Σ' → ℕ
ℕ⟦ CONST n ⟧ σ = n
ℕ⟦ VAR x ⟧ σ = σ x
ℕ⟦ n PLUS m ⟧ σ = ℕ⟦ n ⟧ σ + ℕ⟦ m ⟧ σ
ℕ⟦ n TIMES m ⟧ σ = ℕ⟦ n ⟧ σ * ℕ⟦ m ⟧ σ
ℕ⟦ n MINUS m ⟧ σ = ℕ⟦ n ⟧ σ ∸ ℕ⟦ m ⟧ σ



-- Id = {(x, y) | x , y ∈ A ∧ x ≡ y }
Id : {A : Set} → A → A → Set
Id x y = x ≡ y


-- R ∪ S = {(x, y) | (x, y) ∈ R v (x, y) ∈ S}
_∪_ : {A : Set} {B : Set}
  → (A → B → Set) 
  → (A → B → Set) 
  ---------------
  → (A → B → Set)
(R ∪ S) x y = R x y ⊎ S x y


-- R ◯ S = {(x, y) | ∃z: (x,z) ∈ R ∧ (z,y) ∈ S}
_◯_ : {A : Set} {B : Set} {C : Set} 
  → (A → B → Set) 
  → (B → C → Set) 
  ---------------
  → (A → C → Set)

(R ◯ S) x y = ∃ λ z → R x z × S z y
  -- it's the same as Σ _ (λ z → R x z × S z y)

-- R ⇃ P = {(x, y) | (x, y) ∈ R ∧ P x}
_⇃_ : {A : Set} {B : Set} 
  → (A → B → Set) 
  → (A → Set) 
  ---------------
  → (A → B → Set)

(R ⇃ P) x y = R x y × P x

denote : Cmd → Σ' → Σ' → Set
denote SKIP = Id
denote (x ::= e) σ σ' = Σ Σ' (λ σ'' → σ'' ≡ σ  × σ' ≡ (σ [ x ↦ ℕ⟦ e ⟧ σ ]))
  -- denote (x ::= e) = {(σ, σ') : σ' ≡ (σ [ x ↦ ℕ⟦ e ⟧ σ ]) }
denote (cmd :: cmd') = (denote cmd) ◯ (denote cmd')
denote WHILE x DO cmd DONE = {!   !}

-- fixpoint
-- x = f x






Monotonic : {A B : Set} 

  → (A → A → Set)
  → (B → B → Set) 
  → (A → B)
  ---------------
  → Set
Monotonic _≤_ _≤'_ f  =  ∀ {x y} 

  →  x ≤ y 
  ---------------
  →  f x ≤' f y

_∈_ : {A : Set} 
  → A
  → (A → Set)
  -----------
  → Set

_∈'_ : {A : Set} 
  → (A → Set)
  → ((A → Set) → Set)
  -----------
  → Set

Y ∈' X = X Y



x ∈ X = X x
 
_⊆_ : {A : Set}
    → (A → Set)
    → (A → Set)
    ------------
    → Set

X ⊆ Y = ∀ {x} 
  →  x ∈ X 
  ---------
  →  x ∈ Y

-- ∩ X = { x | Y ∈ X  ⇒ x ∈ Y }

∩ : {A : Set}
    → ((A → Set) → Set)
    -------------------
    → Set₁ 

∩ {A} X = ∀ {Y : A → Set} {x : A} 

  → Y ∈' X
  --------
  → x ∈ Y


-- relations 
-- reflex:         ∀ x     . xRx
-- simmetric:      ∀ x y   . xRy ⇒ yRx
-- antisimmetric:  ∀ x y   . xRy ∧ yRx ⇒  x ≡ y
-- transistive:    ∀ x y z . xRy ∧ yRz ⇒  xRz 
-- total:          ∀ x y   . xRy v yRx 
-- 
-- A relation R is
-- Preorder: reflexive and transitive.
-- Partial order: preorder and antisimmetric.
-- Total order: partial order and total

Reflex : {A : Set} 
  
  → (A → A →  Set) 
  ---------------
  → Set

Reflex _R_ = ∀ {x} → x R x



Sym : {A : Set} 
  
  → (A → A →  Set) 
  ---------------
  → Set

Sym _R_ =  ∀ {x y} 

  → x R y
  --------
  → y R x


Antisym : {A : Set} 
  
  → (A → A →  Set)
  → (A → A →  Set) 
  ---------------
  → Set

Antisym _R_ _≈_ =  ∀ {x y} 

  → x R y
  → y R x
  --------
  → y ≈ x


Trans : {A : Set} 
  
  → (A → A →  Set) 
  ---------------
  → Set

Trans _R_ = ∀ {x y z}

  → x R y
  → y R z
  --------
  → x R z

  

record IsPartialOrder {A : Set} (_≤_ _≈_ : A → A → Set) : Set where
  field
    reflex      : Reflex  _≤_
    transitive  : Trans _≤_ 
    antisym     : Antisym _≤_ _≈_


record IsCompleteLattice {A : Set} 
  (_≤_ _≈_ : A → A → Set) 
  (Π : (A → Set) → A) : Set₁ where
  field
    isPartialOrder : IsPartialOrder _≤_ _≈_
    lub : ∀ {X} {x} → x ∈ X → Π X ≤ x
    gtLub : ∀ {X} {y} → (∀ {x} → x ∈ X → y ≤ x) → y ≤ Π X



lfp : {A : Set} 
  → (_≤_ _≈_ : A → A → Set)
  → (Π : (A → Set) → A) 
  → (IsCompleteLattice _≤_ _≈_ Π)
  → (A → A) 
  → A
lfp _≤_ _ Π _ f = Π (λ x → f x ≤ x)


{-
lemma lfp_le {α : Type} [complete_lattice α] (f : α → α)
    (a : α) (h : f a ≤ a) :
  lfp f ≤ a :=
complete_lattice.Inf_le _ _ h

-}

lfpLe : {A : Set} 
  → (_≤_ _≈_ : A → A → Set)
  → (Π : (A → Set) → A) 
  → (cl : IsCompleteLattice _≤_ _≈_ Π)
  → (f : A → A) 
  → (x : A)
  → (h : f x ≤ x)
  ---------------
  → lfp _≤_ _≈_ Π cl f ≤ x
lfpLe _≤_ _≈_ Π cl f x h = IsCompleteLattice.lub cl h


Lelfp : {A : Set} 

  → (_≤_ _≈_ : A → A → Set)
  → (Π : (A → Set) → A) 
  → (cl : IsCompleteLattice _≤_ _≈_ Π)
  → (f : A → A) 
  → (x : A)
  → (h : ∀ {x'} →  f x' ≤ x' → x ≤ x')
  -------------------------------------
  → x ≤ lfp _≤_ _≈_ Π cl f

Lelfp _≤_ _≈_ Π cl f x h = IsCompleteLattice.gtLub cl h

-- lfp is a fixpoint
isFixpoint : {A : Set} 

  → (_≤_ _≈_ : A → A → Set) 
  → (Π : (A → Set) → A) 
  → (cl : IsCompleteLattice _≤_ _≈_ Π)
  → (f : A → A)
  → (Monotonic _≤_ _≤_ f)
  --------------------------------------------
  →  (f (lfp _≤_ _≈_ Π cl f)) ≈ (lfp _≤_ _≈_ Π cl f)  
  
isFixpoint _≤_ _≈_ Π cl f m  = fx≈x
  where
    x = f (lfp _≤_ _≈_ Π cl f)
        
    x≤fx = lfpLe _≤_ _≈_ Π cl f x (m
        (IsCompleteLattice.gtLub cl
          (λ z →
            IsPartialOrder.transitive (IsCompleteLattice.isPartialOrder cl)
            (m (IsCompleteLattice.lub cl z)) z)))
    
    fx≤x = Lelfp _≤_ _≈_ Π cl f x λ z →
      IsPartialOrder.transitive (IsCompleteLattice.isPartialOrder cl)
      (m (IsCompleteLattice.lub cl z)) z
    
    antisim = IsPartialOrder.antisym (IsCompleteLattice.isPartialOrder cl) 
    
    -- f x ≤ x ∧ x ≤ f x ⇒ f x ≈ x
    fx≈x = antisim x≤fx fx≤x 

    
    