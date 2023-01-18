module Cats where
import Relation.Binary.PropositionalEquality as Eqq
open Eqq using (_≡_; refl; cong; cong₂; sym ; trans; cong-app)
open Eqq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

id : {A : Set} → A → A
id x = x


_∘_ : {A B C : Set}

  → (B → C)
  → (A → B)
  ----------
  → (A → C)

g ∘ f = λ x → g (f x)


------------------------------------------------------------------------
--                     Functor as type class                          --
------------------------------------------------------------------------

record Functor (F : Set → Set) : Set₁ where
  field
    --Operations---------------------------------
    fmap : ∀ {A B} → (A → B) → F A → F B

  field
    --Laws---------------------------------------
    law-id : ∀ {A} → (x : F A) → (fmap id x) ≡ x
    law-comp : ∀ {A B C} 

      → {g : B → C}
      → {f : A → B} 
      → (x : F A)
      -------------------------------------------
      →  (fmap (g ∘ f) x) ≡ ((fmap g ∘ fmap f) x)

open Functor {{...}} public




--Maybe Functor---------------------------------------------------------

data Maybe (A : Set) : Set where
  nothing : Maybe A 
  just : A → Maybe A 

--Maybe fmap------------------------------------------------------------
fmap-maybe : {A B : Set} → (A → B) → Maybe A → Maybe B
fmap-maybe f nothing = nothing
fmap-maybe f (just x) = just (f x)

--Maybe law-id----------------------------------------------------------
law-id-maybe : ∀ {A : Set} (x : Maybe A) → fmap-maybe id x ≡ x
law-id-maybe nothing =
  begin
    fmap-maybe id nothing
  ≡⟨ refl ⟩
    nothing
  ∎
law-id-maybe (just x) =
  begin
    fmap-maybe id (just x)
  ≡⟨ refl ⟩
    just x
  ∎
  
--Maybe law-comp--------------------------------------------------------
law-comp-maybe :  

  ∀ {A B C : Set}
  {g : B → C} 
  {f : A → B}       
  (x : Maybe A)
  --------------------------------------------------------
  → fmap-maybe (g ∘ f) x ≡ (fmap-maybe g ∘ fmap-maybe f) x
  
law-comp-maybe nothing = refl
law-comp-maybe {A} {B} {C} {g} {f} (just x) =
  begin
    fmap-maybe (g ∘ f) (just x)
  ≡⟨⟩
    just ((g ∘ f) x)
  ≡⟨⟩
    just (g (f x))
  ≡⟨⟩
    fmap-maybe g (just (f x))
  ≡⟨⟩
    fmap-maybe g (fmap-maybe f (just x))
  ≡⟨ refl ⟩
    (fmap-maybe g ∘ fmap-maybe f) (just x)
  ∎

  
instance
  MaybeFunctor : Functor Maybe
  MaybeFunctor = record {
      fmap = fmap-maybe 
    ; law-id = law-id-maybe 
    ; law-comp = law-comp-maybe
    }



--List Functor----------------------------------------------------------
data List (A : Set) : Set where
  nil : List A 
  cons : A → List A → List A

--List fmap-------------------------------------------------------------
fmap-list : {A B : Set} → (A → B) → List A → List B
fmap-list f nil = nil
fmap-list f (cons x xs) = cons (f x) (fmap-list f xs)

--List law-id-----------------------------------------------------------
law-id-list : {A : Set} (xs : List A) → fmap-list id xs ≡ xs
law-id-list nil = refl
law-id-list (cons x xs) = begin
    fmap-list id (cons x xs)
  ≡⟨⟩
    cons x (fmap-list id xs)
  ≡⟨ cong ((λ ys → cons x ys )) (law-id-list xs) ⟩
    cons x xs
  ∎

--List law-comp---------------------------------------------------------
law-comp-list : 

  {A B C : Set} 
  {g : B → C} 
  {f : A → B}
  (xs : List A)
  ------------------------------------------------------- 
  → fmap-list (g ∘ f) xs ≡ (fmap-list g ∘ fmap-list f) xs
  
law-comp-list nil = refl
law-comp-list {A} {B} {C} {g} {f} (cons x xs) =
  begin
    fmap-list (g ∘ f) (cons x xs)
  ≡⟨⟩
    cons ((g ∘ f) x) (fmap-list (g ∘ f) xs)
  ≡⟨ cong (λ ys → cons ((g ∘ f) x) ys  ) (law-comp-list xs) ⟩
    (fmap-list g ∘ fmap-list f) (cons x xs)
  ∎ 

instance
  ListFunctor : Functor List
  ListFunctor = record {
      fmap = fmap-list 
    ; law-id = law-id-list 
    ; law-comp = law-comp-list
    }
    

------------------------------------------------------------------------
--                           Category theory                          --
------------------------------------------------------------------------

--Category definition---------------------------------------------------

record Category : Set₂ where
  infix  4 _⇒_
  infixr 9 _◯_

  field
    Obj : Set₁ 
    _⇒_ : Obj → Obj → Set
    
    id'  : ∀ {A} → (A ⇒ A)
    _◯_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
  
  field
    -- 
    assoc : ∀ {A B C D} 
      {f : A ⇒ B} 
      {g : B ⇒ C} 
      {h : C ⇒ D} 
      
      → (h ◯ g) ◯ f ≡ h ◯ (g ◯ f)

    identityˡ : ∀ {A B} {f : A ⇒ B} → id' ◯ f ≡  f
    identityʳ : ∀ {A B} {f : A ⇒ B} → f ◯ id' ≡ f


--Notation--------------------------------------------------------------
infix 10  _[_,_] _[_∘_]

-- 𝒞 [ A , B ] is Hom𝒞(A , B) 
_[_,_] : (𝒞 : Category) → (X : Category.Obj 𝒞) → (Y : Category.Obj 𝒞) → Set
_[_,_] = Category._⇒_

-- 𝒞 [ f ∘ g ] for f g composables arrows of 𝒞
_[_∘_] : (𝒞 : Category) → ∀ {X Y Z} (f : 𝒞 [ Y , Z ]) → (g : 𝒞 [ X , Y ]) → 𝒞 [ X , Z ]
_[_∘_] = Category._◯_


--𝒯𝒴𝒫ℰ𝒮 category--------------------------------------------------------
𝒯𝒴𝒫ℰ𝒮 : Category
𝒯𝒴𝒫ℰ𝒮 = record {
      Obj = Set
    ; _⇒_ = λ A B → (A → B) 
    ; id' = id
    ; _◯_ = _∘_
    
    -- laws
    ; assoc = refl
    ; identityˡ = refl
    ; identityʳ = refl
  }



--Functor definition----------------------------------------------------
record IsFunctor (𝒞 𝒟 : Category) : Set₂  where
  private module 𝒞 = Category 𝒞
  private module 𝒟 = Category 𝒟

  field
    F₀ : 𝒞.Obj → 𝒟.Obj
    F₁ : ∀ {A B} (f : 𝒞 [ A , B ]) → 𝒟 [ F₀ A , F₀ B ]
    
    identity  : ∀ {A} →  F₁ (𝒞.id' {A}) ≡ 𝒟.id'
    homomorphism : ∀ {X Y Z}
     
      {f : 𝒞 [ X , Y ]} 
      {g : 𝒞 [ Y , Z ]}
      --------------------------------------
      → F₁ (𝒞 [ g ∘ f ]) ≡ 𝒟 [ F₁ g ∘ F₁ f ]
    
    F-resp-≡ : ∀ {A B} 
      {f g : 𝒞 [ A , B ]}
      
      → f ≡  g  
      --------------------
      → F₁ f ≡  F₁ g 

--Endofunctor definition------------------------------------------------
Endofunctor = λ 𝒞 → IsFunctor 𝒞 𝒞


maybe-functor : Endofunctor 𝒯𝒴𝒫ℰ𝒮
maybe-functor = record
  {   F₀ = Maybe
    ; F₁ = fmap
    ; identity = extensionality proof-identity
    ; homomorphism = extensionality proof-homomorphism
    ; F-resp-≡ = proof-F-resp-≡
  }
  where
    --Maybe identity----------------------------------------------------
    proof-identity : {A : Set} 
    
      → (x : Maybe A) 
      --------------------------------------------
      → fmap-maybe (Category.id' 𝒯𝒴𝒫ℰ𝒮) x ≡ id x
      
    proof-identity nothing = refl
    proof-identity (just x) = refl

    --Maybe homomorphism------------------------------------------------
    proof-homomorphism : {X Y Z : Set} 
    
      {f : 𝒯𝒴𝒫ℰ𝒮 [ X , Y ]}
      {g : 𝒯𝒴𝒫ℰ𝒮 [ Y , Z ]}
      → (x : Maybe X)
      ----------------------------------------------------
      → ((fmap-maybe (𝒯𝒴𝒫ℰ𝒮 [ g ∘ f ])) x) 
      ≡ ((𝒯𝒴𝒫ℰ𝒮 [ fmap-maybe g ∘ fmap-maybe f ]) x)
    
    proof-homomorphism nothing = refl
    proof-homomorphism (just x) = refl

    --Maybe F-resp-≡----------------------------------------------------
    proof-F-resp-≡ : {A B : Set} {f g : 𝒯𝒴𝒫ℰ𝒮 [ A , B ]} 

      → f ≡ g 
      -----------------------------
      → fmap-maybe f ≡ fmap-maybe g
      
    proof-F-resp-≡ f≡g = cong (λ z → fmap-maybe z) f≡g
    