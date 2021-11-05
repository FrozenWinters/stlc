{-# OPTIONS --cubical #-}

module contextual where

open import lists public

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

-- This new definition of a contextual category arose as a way to de-boilerplate the code;
-- it is the most natural variation of the definition to use in an implementation.

record Contextual (ℓ₁ ℓ₂ : Level) : Type (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    ty : Type ℓ₁
    
  ctx = RL ty
  
  field
    tm : ctx → ty → Type ℓ₂

  tms = IL tm

  infixl 30 _⟦_⟧
  field
    _⟦_⟧ : {Γ Δ : ctx} {A : ty} → tm Δ A → tms Γ Δ → tm Γ A

  infixl 20 _⊚_
  _⊚_ : {Γ Δ Σ : ctx} → tms Δ Σ → tms Γ Δ → tms Γ Σ
  σ ⊚ τ = mapIL _⟦ τ ⟧ σ

  field
    𝒾𝒹 : (Γ : ctx) → tms Γ Γ
    𝒾𝒹L : {Γ Δ : ctx} (σ : tms Γ Δ) → 𝒾𝒹 Δ ⊚ σ ≡ σ
    𝒾𝒹⟦⟧ : {Γ : ctx} {A : ty} (t : tm Γ A) → t ⟦ 𝒾𝒹 Γ ⟧ ≡ t
    ⟦⟧⟦⟧ : {Γ Δ Σ : ctx} {A : ty} (t : tm Σ A) (σ : tms Δ Σ) (τ : tms Γ Δ) →
      t ⟦ σ ⟧ ⟦ τ ⟧ ≡ t ⟦ σ ⊚ τ ⟧
    isSetTm : {Γ : ctx} {A : ty} → isSet (tm Γ A)

  𝒾𝒹R : {Γ Δ : ctx} (σ : tms Γ Δ) → σ ⊚ 𝒾𝒹 Γ ≡ σ
  𝒾𝒹R ! = refl
  𝒾𝒹R (σ ⊕ t) i = 𝒾𝒹R σ i ⊕ 𝒾𝒹⟦⟧ t i

  ⊚Assoc : {Γ Δ Σ Ω : ctx} (σ : tms Σ Ω) (τ : tms Δ Σ) (μ : tms Γ Δ) →
    σ ⊚ τ ⊚ μ ≡ σ ⊚ (τ ⊚ μ)
  ⊚Assoc ! τ μ = refl
  ⊚Assoc (σ ⊕ t) τ μ i = ⊚Assoc σ τ μ i ⊕ ⟦⟧⟦⟧ t τ μ i

  private
    module P = ILPath tm isSetTm

  isSetTms = P.isSetTms

  -- Every contextual category has an ambient category of contexts and terms

  open Precategory hiding (_∘_)

  ambCat : Precategory ℓ₁ (ℓ₁ ⊔ ℓ₂)
  ob ambCat = ctx
  Hom[_,_] ambCat Γ Δ = tms Γ Δ
  Precategory.id ambCat Γ = 𝒾𝒹 Γ
  _⋆_ ambCat τ σ = σ ⊚ τ
  ⋆IdL ambCat = 𝒾𝒹R
  ⋆IdR ambCat = 𝒾𝒹L
  ⋆Assoc ambCat μ τ σ = ⊚Assoc σ τ μ ⁻¹

  instance
    isCatAmbCat : isCategory ambCat
    isSetHom isCatAmbCat = isSetTms

  -- ∅ is automatically the terminal object with unique morphism !

  !η : {Γ : ctx} (σ : tms Γ ∅) → ! ≡ σ
  !η ! = refl

  -- Contextual categories automatically have products

  π : {Γ : ctx} {A : ty} → tms (Γ ⊹ A) Γ
  π {Γ} {A} = πIL (𝒾𝒹 (Γ ⊹ A))

  𝑧 : {Γ : ctx} {A : ty} → tm (Γ ⊹ A) A
  𝑧 {Γ} {A} = 𝑧IL (𝒾𝒹 (Γ ⊹ A))

  𝒾𝒹η : {Γ : ctx} {A : ty} → π ⊕ 𝑧 ≡ 𝒾𝒹 (Γ ⊹ A) 
  𝒾𝒹η {Γ} {A} = π𝑧ηIL (𝒾𝒹 (Γ ⊹ A))

  π𝑧η : {Γ Δ : ctx} {A : ty} (σ : tms Γ (Δ ⊹ A)) →
    (π ⊚ σ) ⊕ (𝑧 ⟦ σ ⟧) ≡ σ
  π𝑧η {Γ} {Δ} {A} σ =
    π ⊚ σ ⊕ 𝑧 ⟦ σ ⟧
      ≡⟨ ap (_⊚ σ) 𝒾𝒹η ⟩
    𝒾𝒹 (Δ ⊹ A) ⊚ σ
      ≡⟨ 𝒾𝒹L σ ⟩
    σ
      ∎

  πβ : {Γ Δ : ctx} {A : ty} (σ : tms Γ (Δ ⊹ A)) →
    π ⊚ σ ≡ πIL σ
  πβ σ = ap πIL (π𝑧η σ)

  𝑧β : {Γ Δ : ctx} {A : ty} (σ : tms Γ (Δ ⊹ A)) →
    𝑧 ⟦ σ ⟧ ≡ 𝑧IL σ
  𝑧β σ = ap 𝑧IL (π𝑧η σ)

  -- The identity function includes with it a notion of internal variables

  data IntVar : ctx → ty → Type ℓ₁ where
    𝑧V : {Γ : ctx} {A : ty} → IntVar (Γ ⊹ A) A
    𝑠V : {Γ : ctx} {A B : ty} → IntVar Γ A → IntVar (Γ ⊹ B) A

  derive : {Γ Δ : ctx} {A : ty} → tms Γ Δ → IntVar Δ A → tm Γ A
  derive σ 𝑧V = 𝑧IL σ
  derive σ (𝑠V v) = derive (πIL σ) v

  makeVar : {Γ : ctx} {A : ty} → IntVar Γ A → tm Γ A
  makeVar {Γ} = derive (𝒾𝒹 Γ)

  IntRen = IL IntVar

  deriveRen : {Γ Δ Σ : ctx} → tms Γ Δ → IntRen Δ Σ → tms Γ Σ
  deriveRen σ = mapIL (derive σ)

  makeRen : {Γ Δ : ctx} → IntRen Γ Δ → tms Γ Δ
  makeRen {Γ} = deriveRen (𝒾𝒹 Γ)

  deriveMap : {Γ Δ Σ : ctx} (f : {A : ty} → tm Γ A → tm Δ A) (σ : tms Γ Σ) {A : ty}
    (v : IntVar Σ A) → derive (mapIL f σ) v ≡ f (derive σ v)
  deriveMap f (σ ⊕ t) 𝑧V = refl
  deriveMap f (σ ⊕ t) (𝑠V v) = deriveMap f σ v

  derive⟦⟧ : {Γ Δ Σ : ctx} {A : ty} (v : IntVar Σ A) (σ : tms Δ Σ) (τ : tms Γ Δ) →
    derive σ v ⟦ τ ⟧ ≡ derive (σ ⊚ τ) v
  derive⟦⟧ 𝑧V σ τ =
    𝑧IL σ ⟦ τ ⟧
      ≡⟨ ap _⟦ τ ⟧ (𝑧β σ ⁻¹) ⟩
    𝑧 ⟦ σ ⟧ ⟦ τ ⟧
      ≡⟨ ⟦⟧⟦⟧ 𝑧 σ τ ⟩
    𝑧 ⟦ σ ⊚ τ ⟧
      ≡⟨ 𝑧β (σ ⊚ τ) ⟩
    𝑧IL (σ ⊚ τ)
      ∎
  derive⟦⟧ (𝑠V v) σ τ =
    derive (πIL σ) v ⟦ τ ⟧
      ≡⟨ (λ i → derive (πβ σ (~ i)) v ⟦ τ ⟧) ⟩
    derive (π ⊚ σ) v ⟦ τ ⟧
      ≡⟨ ap _⟦ τ ⟧ (derive⟦⟧ v π σ ⁻¹) ⟩
    derive π v ⟦ σ ⟧ ⟦ τ ⟧
      ≡⟨ ⟦⟧⟦⟧ (derive π v) σ τ ⟩
    derive π v ⟦ σ ⊚ τ ⟧
      ≡⟨ derive⟦⟧ v π (σ ⊚ τ) ⟩
    derive (π ⊚ (σ ⊚ τ)) v
      ≡⟨ (λ i → derive (πβ (σ ⊚ τ) i) v) ⟩
    derive (πIL (σ ⊚ τ)) v
      ∎

  varβ : {Γ Δ : ctx} {A : ty} (v : IntVar Δ A) (σ : tms Γ Δ) →
    makeVar v ⟦ σ ⟧ ≡ derive σ v
  varβ {Γ} {Δ} v σ =
    derive (𝒾𝒹 Δ) v ⟦ σ ⟧
      ≡⟨ derive⟦⟧ v (𝒾𝒹 Δ) σ ⟩
    derive (𝒾𝒹 Δ ⊚ σ) v
      ≡⟨ (λ i → derive (𝒾𝒹L σ i) v) ⟩
    derive σ v
      ∎

  make𝑠V : {Γ : ctx} {A B : ty} (v : IntVar Γ A) →
    makeVar (𝑠V {B = B} v) ≡ makeVar v ⟦ π ⟧
  make𝑠V {Γ} {A} {B} v = varβ v π ⁻¹

  private 
    W₁IntRen : {Γ Δ : ctx} {A : ty} → IntRen Γ Δ → IntRen (Γ ⊹ A) Δ
    W₁IntRen σ = mapIL 𝑠V σ

    W₂IntRen : {Γ Δ : ctx} {A : ty} → IntRen Γ Δ → IntRen (Γ ⊹ A) (Δ ⊹ A)
    W₂IntRen σ = W₁IntRen σ ⊕ 𝑧V

    W₁IntRenLem : {Γ Δ Σ : ctx} {A : ty} (σ : tms Γ Δ) (t : tm Γ A) (v : IntRen Δ Σ) →
      deriveRen (σ ⊕ t) (W₁IntRen v) ≡ deriveRen σ v
    W₁IntRenLem σ t ! = refl
    W₁IntRenLem σ t (τ ⊕ v) i = W₁IntRenLem σ t τ i ⊕ derive σ v

  idIntRen : (Γ : ctx) → IntRen Γ Γ
  idIntRen ∅ = !
  idIntRen (Γ ⊹ A) = W₂IntRen (idIntRen Γ)

  -- Taking apart the variables and putting them back together does nothing

  derive𝒾𝒹 : {Γ Δ : ctx} (σ : tms Γ Δ) →
    deriveRen σ (idIntRen Δ) ≡ σ
  derive𝒾𝒹 ! = refl
  derive𝒾𝒹 {Γ} {Δ ⊹ A} (σ ⊕ t) =
    deriveRen (σ ⊕ t) (W₁IntRen (idIntRen Δ)) ⊕ t
      ≡⟨ ap (_⊕ t) (W₁IntRenLem σ t (idIntRen Δ)) ⟩
    deriveRen σ (idIntRen Δ) ⊕ t
      ≡⟨ ap (_⊕ t) (derive𝒾𝒹 σ) ⟩
    σ ⊕ t
      ∎

  𝒾𝒹η₂ : {Γ : ctx} → makeRen (idIntRen Γ) ≡ 𝒾𝒹 Γ
  𝒾𝒹η₂ {Γ} = derive𝒾𝒹 (𝒾𝒹 Γ)

-- The idea is that a contextual functor preserves the contextual structure

record ContextualFunctor (𝒞 : Contextual ℓ₁ ℓ₂) (𝒟 : Contextual ℓ₃ ℓ₄)
       : Type (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  open Contextual

  private
    module C = Contextual 𝒞
    module D = Contextual 𝒟
  
  field
    CF-ty : ty 𝒞 → ty 𝒟

  CF-ctx : ctx 𝒞 → ctx 𝒟
  CF-ctx Γ = mapRL CF-ty Γ

  field
    CF-tm : {Γ : ctx 𝒞} {A : ty 𝒞} → tm 𝒞 Γ A → tm 𝒟 (CF-ctx Γ) (CF-ty A)

  CF-tms : {Γ Δ : ctx 𝒞} → tms 𝒞 Γ Δ → tms 𝒟 (CF-ctx Γ) (CF-ctx Δ)
  CF-tms σ = mapIL₁ CF-tm σ

  field
    CF-id : {Γ : ctx 𝒞} → CF-tms (𝒾𝒹 𝒞 Γ) ≡ 𝒾𝒹 𝒟 (CF-ctx Γ)
    CF-sub : {Γ Δ : ctx 𝒞} {A : ty 𝒞} (t : tm 𝒞 Δ A) (σ : tms 𝒞 Γ Δ) →
      CF-tm (t C.⟦ σ ⟧) ≡ CF-tm t D.⟦ CF-tms σ ⟧

  CF-comp : {Γ Δ Σ : ctx 𝒞} (σ : tms 𝒞 Δ Σ) (τ : tms 𝒞 Γ Δ) →
    CF-tms (σ C.⊚ τ) ≡ (CF-tms σ) D.⊚ (CF-tms τ)
  CF-comp ! τ = refl
  CF-comp (σ ⊕ t) τ i = CF-comp σ τ i ⊕ CF-sub t τ i

  open Functor

  -- A contextual functor induces a functor between the ambient categories

  ambFun : Functor (ambCat 𝒞) (ambCat 𝒟)
  F-ob ambFun = CF-ctx
  F-hom ambFun = CF-tms
  F-id ambFun = CF-id
  F-seq ambFun τ σ = CF-comp σ τ
