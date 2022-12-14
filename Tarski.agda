module Tarski where
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
open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Nullary using (¬_)

private
  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level

-- Heterogeneous binary relations

REL : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ lsuc ℓ)
REL A B ℓ = A → B → Set ℓ

-- Homogeneous binary relations

Rel : Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
Rel A ℓ = REL A A ℓ

-- A unary relation is a predicate 
Pred : Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
Pred A ℓ = A → Set ℓ

-- Set type as in lean
SET : Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
SET A ℓ = Pred A ℓ

_∈_ : {A : Set a} →  A → SET A ℓ → Set _
x ∈ P = P x



-- In set theory:  for a set A and P a predicate over A (i.e. P ⊆ A), S = {x ∈ A | P x }
-- In type theory: A : Set, P : A → Set and  S = Σ A P

-- Id = {(x, y) | x , y ∈ A ∧ x ≡ y }
Id : {A : Set a} →  A → A → Set a
Id x y = x ≡ y


-- R ∪ S = {(x, y) | (x, y) ∈ R v (x, y) ∈ S}
_∪_ : {A : Set a} {B : Set b}
 
  → REL A B ℓ₁ 
  → REL A B ℓ₂ 
  -------------------
  → REL A B (ℓ₁ ⊔ ℓ₂)
(R ∪ S) x y = R x y ⊎ S x y


-- R ◯ S = {(x, y) | ∃z: (x,z) ∈ R ∧ (z,y) ∈ S}

_◯_ : {A : Set a} {B : Set b} {C : Set c} 

  → REL A B ℓ₁ 
  → REL B C ℓ₂ 
  -------------------------
  → REL A C (b ⊔  ℓ₁ ⊔ ℓ₂ )
  
(R ◯ S) x y = ∃ λ z → R x z × S z y






  -- it's the same as Σ _ (λ z → R x z × S z y)

-- R ⇃ P = {(x, y) | (x, y) ∈ R ∧ P x}
_⇃_ : {A : Set a}  {B : Set b} 

  → REL A B ℓ₁
  → Pred A ℓ₂  
  ---------------
  → REL A B (ℓ₁ ⊔ ℓ₂)

(R ⇃ P) x y = R x y × P x



private
  variable
    _≈_ : {A : Set a} → Rel A ℓ    -- The underlying equality relation





Monotonic : {A : Set a} {B : Set b}

  → Rel A ℓ₁ 
  → Rel B ℓ₂ 
  → (A → B)
  ---------------
  → Set (a ⊔ ℓ₁ ⊔ ℓ₂)

Monotonic _R_ _R'_ f  = ∀ {x y} 

  →  x R y 
  ---------------
  →  f x R' f y


_⊆_ : {A : Set a}
    → SET A ℓ₁
    → SET A ℓ₂ 
    ------------
    → Set (a ⊔ ℓ₁ ⊔ ℓ₂)

X ⊆ Y = ∀ {x} 

  →  x ∈ X 
  ---------
  →  x ∈ Y





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

Reflex : {A : Set a} 
  
  → Rel A ℓ₁ 
  ---------------
  → Set (a ⊔ ℓ₁) 

Reflex _R_ = ∀ {x} → x R x




Sym : {A : Set a} 
  
  → Rel A ℓ₁ 
  ---------------
  → Set _

Sym _R_ =  ∀ {x y} 

  → x R y
  --------
  → y R x


Antisymmetric : {A : Set a}  →  Rel A ℓ₁ → Rel A ℓ₂ → Set _
Antisymmetric _E_ _R_ =  ∀ {x y} 
  
  →  x R y 
  → y R x 
  --------
  → x E y 



Trans : {A : Set a} 
  
  → Rel A ℓ₁  
  ---------------
  → Set _

Trans _R_ = ∀ {x y z}

  → x R y
  → y R z
  --------
  → x R z

  
module Structures
  {a ℓ ℓ₃} {A : Set a} -- The underlying set
  (_≈_ : Rel A ℓ)   -- The underlying equality relation
  where


  record IsPartialOrder (_≤_ : Rel A ℓ₂  ) :  Set (a ⊔ ℓ ⊔ ℓ₂) where
    field
      reflex      : Reflex  _≤_
      transitive  : Trans _≤_ 
      antisym     : Antisymmetric _≈_ _≤_
  
  record IsCompleteLattice (_≤_ : Rel A ℓ₂) (Π : SET A ℓ₂ → A) : Set (a ⊔  ℓ ⊔ lsuc ℓ₂) where
    field
      isPartialOrder : IsPartialOrder _≤_
      glb : ∀ {X} {x} → x ∈ X → Π X ≤ x
      gtGlb : ∀ {X} {y} → (∀ {x} → x ∈ X → y ≤ x) → y ≤ Π X
  
  lfp :
       (_≤_ : Rel A ℓ₃ ) 
    → (Π : SET A ℓ₃ → A) 
    → (IsCompleteLattice _≤_  Π)
    → (A → A)
    --------------------------------
    → A
  lfp _≤_ Π cl f = Π (λ x → f x ≤ x)

  lfpLe : 
      (_≤_ : Rel A ℓ₃ ) 
    → (Π : SET A ℓ₃ → A) 
    → (cl : IsCompleteLattice _≤_ Π)
    → (f : A → A) 
    → (x : A)
    → (h : f x ≤ x)
    ---------------------
    → lfp _≤_ Π cl f ≤ x
  lfpLe _≤_ Π cl f x h = IsCompleteLattice.glb cl h

  Lelfp : 
      (_≤_ : Rel A ℓ₃ ) 
    → (Π : SET A ℓ₃ → A) 
    → (cl : IsCompleteLattice _≤_ Π)
    → (f : A → A) 
    → (x : A)
    → (h : ∀ {x'} →  f x' ≤ x' → x ≤ x')
    -------------------------------------
    → x ≤ lfp _≤_ Π cl f

  Lelfp _≤_ Π cl f x h = IsCompleteLattice.gtGlb cl h

  isFixpoint : 
      (_≤_ : Rel A ℓ₃ ) 
    → (Π : SET A ℓ₃ → A) 
    → (cl : IsCompleteLattice _≤_ Π)
    → (f : A → A) 
    → (Monotonic _≤_ _≤_ f)
    --------------------------------------------
    →  (f (lfp _≤_ Π cl f)) ≈ (lfp _≤_ Π cl f)  
  
  isFixpoint _≤_ Π cl f f-monotone  = fx≈x
    where
      x = f (lfp _≤_ Π cl f)
      
      x≤fx : lfp _≤_ Π cl f ≤ f (lfp _≤_ Π cl f)
      x≤fx = lfpLe _≤_ Π cl f x (f-monotone
          (IsCompleteLattice.gtGlb cl
            (λ z → IsPartialOrder.transitive (IsCompleteLattice.isPartialOrder cl)
              (f-monotone (IsCompleteLattice.glb cl z)) z)))
      
      fx≤x : f (lfp _≤_ Π cl f) ≤ lfp _≤_ Π cl f  
      fx≤x = Lelfp _≤_ Π cl f x λ z →
        IsPartialOrder.transitive (IsCompleteLattice.isPartialOrder cl)
        (f-monotone (IsCompleteLattice.glb cl z)) z
      
      antisim = IsPartialOrder.antisym (IsCompleteLattice.isPartialOrder cl) 
      
      -- f x ≤ x ∧ x ≤ f x ⇒ f x ≈ x
      fx≈x : f (lfp _≤_ Π cl f) ≈ (lfp _≤_ Π cl f)
      fx≈x = antisim fx≤x x≤fx




  record Sigma (A : Set) (B : A → Set) : Set where
    constructor _,_
    field fst : A
          snd : B fst


  syntax Sigma A (λ x → P) = [ x ∈ A :: P ]

  Sucs = [ (x , y) ∈ ℕ × ℕ :: y ≡ x + 1 ]

  m : Sucs
  m = ( (2 , 3) , refl ) 

  Var = String
  Σ' = Var → ℕ



  data Arith : Set where
    CONST : ℕ → Arith
    VAR : Var → Arith
    _PLUS_ : Arith → Arith → Arith
    _TIMES_ : Arith → Arith → Arith
    _MINUS_ : Arith → Arith → Arith

  data Boolean : Set where
    TRUE : Boolean
    FALSE : Boolean

  B⟦_⟧ : Boolean → Σ' → Bool
  B⟦ TRUE ⟧ _ = true
  B⟦ FALSE ⟧ _ = false

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
  


  T = Rel Σ' lzero 

  ⋂ : ∀ (I : SET T lzero) → {X : T} → T 
  ⋂ I {X} = λ σ σ' → ( I X → X σ σ')
  
  _⊆'_ : Rel T lzero
  X ⊆' Y = ∀ {σ σ'} →  X σ σ' → Y σ σ' 
  


  
  denote : ∀ {X : T} →  Cmd → Σ' → Σ' → Set
  denote {X} (SKIP) σ σ' = σ ≡ σ' 
  denote {X} (x ::= e) σ σ' = σ' ≡ (σ [ x ↦ ℕ⟦ e ⟧ σ ])
  denote {X} (cmd :: cmd') = (denote {X} cmd ) ◯ (denote {X} cmd')
  denote {X} (WHILE b DO cmd DONE)  = least-fixpoint {X} (W B⟦ b ⟧ (denote {X} cmd) )
    where
              
      W : (Σ' → Bool) → T → ( T → T )
      W cond d d' = λ σ σ' → 
        if cond σ then 
          (d ◯ d') σ σ'
        else 
          σ ≡ σ'
      
      least-fixpoint :  ∀ {X : T} → (T → T) → T 
      least-fixpoint {X} f =  ⋂ (λ x → f x ⊆' x) {X}